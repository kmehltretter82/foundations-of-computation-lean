import FoC.Computability.Compiler.Core.FiniteRecognizer.ExactFuel.StrictProbe.StageInput.TwoBlankCompactor
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.CleanupShapes

set_option doc.verso true

/-!
# Contextual product two-blank packing

Exact contextual runs for the existing two-blank compactor. A single blank
separates the retained product prefix from the protected-frame header. The
compactor stops on that blank and never reads the retained prefix cells.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel
namespace StrictProbe
namespace ProductCleanup
namespace Pack

open SerializedFieldComposer

abbrev gapCell : Option MachineCodeSymbol :=
  StageInput.TwoBlankCompactor.gapCell

def seekTape (outerLeft : List (Option MachineCodeSymbol))
    (remaining crossed body : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remaining with
  | [] =>
      { left := List.append (crossed.map some) (none :: outerLeft)
        head := none
        right := none :: body.map some }
  | current :: rest =>
      { left := List.append (crossed.map some) (none :: outerLeft)
        head := some current
        right := List.append (rest.map some)
          (none :: none :: body.map some) }

def seekConfig (outerLeft : List (Option MachineCodeSymbol))
    (remaining crossed body : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control :=
  StageInput.TwoBlankCompactor.config .seek
    (seekTape outerLeft remaining crossed body)

def rawGapSource (outerLeft : List (Option MachineCodeSymbol))
    (leftRev body : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol DeleteBlock.Control where
  state := .erase (DeleteBlock.optionalGap gapCell)
  tape :=
    { left := List.append (leftRev.map some) (none :: outerLeft)
      head := none
      right := none :: body.map some }

def gapSource (outerLeft : List (Option MachineCodeSymbol))
    (leftRev body : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control :=
  DeleteRestagedMachine.editConfig
    (rawGapSource outerLeft leftRev body)

def compactConfig
    (c : TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control) :
    TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control :=
  StageInput.TwoBlankCompactor.compactConfig c

def pullTape (outerLeft : List (Option MachineCodeSymbol))
    (leftRev rest : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := List.append
          (List.replicate (DeleteBlock.optionalGap gapCell).val none)
          (List.append (leftRev.map some) (none :: outerLeft))
        head := none
        right := [] }
  | current :: suffix =>
      { left := List.append
          (List.replicate (DeleteBlock.optionalGap gapCell).val none)
          (List.append (leftRev.map some) (none :: outerLeft))
        head := some current
        right := suffix.map some }

def pullConfig (outerLeft : List (Option MachineCodeSymbol))
    (leftRev rest : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol DeleteBlock.Control where
  state := .pull
  tape := pullTape outerLeft leftRev rest

def exitTape (outerLeft : List (Option MachineCodeSymbol))
    (wordRev : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := List.append
      (List.replicate ((DeleteBlock.optionalGap gapCell).val - 1) none)
      (List.append (wordRev.map some) (none :: outerLeft))
    head := none
    right := [none] }

def exitConfig (outerLeft : List (Option MachineCodeSymbol))
    (wordRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol DeleteBlock.Control where
  state := .halt
  tape := exitTape outerLeft wordRev

theorem erase_two_run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (leftRev body : Word MachineCodeSymbol) :
    (DeleteBlock.machine (DeleteBlock.optionalGap gapCell)).runConfigExact? 2
        (rawGapSource outerLeft leftRev body) =
      some (pullConfig outerLeft leftRev body) := by
  cases body <;> rfl

theorem pull_symbol_run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol)
    (leftRev suffix : Word MachineCodeSymbol) :
    (DeleteBlock.machine (DeleteBlock.optionalGap gapCell)).runConfigExact?
        5 (pullConfig outerLeft leftRev (current :: suffix)) =
      some (pullConfig outerLeft (current :: leftRev) suffix) := by
  cases current <;> cases suffix <;> rfl

theorem pull_finish_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (leftRev : Word MachineCodeSymbol) :
    (DeleteBlock.machine (DeleteBlock.optionalGap gapCell)).runConfigExact? 1
        (pullConfig outerLeft leftRev []) =
      some (exitConfig outerLeft leftRev) := by
  rfl

theorem pull_run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (leftRev suffix : Word MachineCodeSymbol) :
    (DeleteBlock.machine (DeleteBlock.optionalGap gapCell)).runConfigExact?
        (5 * suffix.length + 1)
        (pullConfig outerLeft leftRev suffix) =
      some (exitConfig outerLeft
        (List.append suffix.reverse leftRev)) := by
  induction suffix generalizing leftRev with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      exact pull_finish_exact outerLeft leftRev
  | cons current suffix ih =>
      rw [show 5 * (current :: suffix).length + 1 =
          5 + (5 * suffix.length + 1) by simp; lia]
      rw [TuringMachine.runConfigExact?_add]
      rw [pull_symbol_run_exact]
      simp only
      rw [ih (current :: leftRev)]
      simp [List.reverse_cons, List.append_assoc]

def rawGapSteps (body : Word MachineCodeSymbol) : Nat :=
  2 + (5 * body.length + 1)

theorem rawGap_run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (leftRev body : Word MachineCodeSymbol) :
    (DeleteBlock.machine (DeleteBlock.optionalGap gapCell)).runConfigExact?
        (rawGapSteps body) (rawGapSource outerLeft leftRev body) =
      some (exitConfig outerLeft
        (List.append body.reverse leftRev)) := by
  unfold rawGapSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [erase_two_run_exact]
  simp only
  exact pull_run_exact outerLeft leftRev body

def restagedExitConfig
    (outerLeft : List (Option MachineCodeSymbol))
    (wordRev : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control :=
  DeleteRestagedMachine.editConfig (exitConfig outerLeft wordRev)

theorem editGap_run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (leftRev body : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine gapCell).runConfigExact?
        (rawGapSteps body) (gapSource outerLeft leftRev body) =
      some (restagedExitConfig outerLeft
        (List.append body.reverse leftRev)) := by
  exact DeleteRestagedMachine.edit_run_of_eq_some
    gapCell _ _ _ (rawGap_run_exact outerLeft leftRev body)

def scanTape (outerLeft : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := outerLeft
        head := none
        right := List.append (crossed.map some)
          (DeleteEndpointRewind.trailingCells gapCell) }
  | current :: rest =>
      { left := List.append (rest.map some) (none :: outerLeft)
        head := some current
        right := List.append (crossed.map some)
          (DeleteEndpointRewind.trailingCells gapCell) }

def scanConfig (outerLeft : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteEndpointRewind.Control where
  state := .scan
  tape := scanTape outerLeft remainingRev crossed

def gateTape (outerLeft : List (Option MachineCodeSymbol))
    (word : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := none :: outerLeft
        head := none
        right := (DeleteEndpointRewind.trailingCells gapCell).tail }
  | first :: rest =>
      { left := none :: outerLeft
        head := some first
        right := List.append (rest.map some)
          (DeleteEndpointRewind.trailingCells gapCell) }

def gateConfig (outerLeft : List (Option MachineCodeSymbol))
    (word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteEndpointRewind.Control where
  state := .gate
  tape := gateTape outerLeft word

def restagedScanConfig
    (outerLeft : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control :=
  DeleteRestagedMachine.rewindConfig
    (scanConfig outerLeft remainingRev crossed)

def restagedGateConfig
    (outerLeft : List (Option MachineCodeSymbol))
    (word : Word MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol
      DeleteRestagedMachine.Control :=
  DeleteRestagedMachine.rewindConfig (gateConfig outerLeft word)

theorem skip_run_exact (outerLeft : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine gapCell).runConfigExact? 2
        (restagedExitConfig outerLeft (first :: rest)) =
      some (restagedScanConfig outerLeft (first :: rest) []) := by
  cases rest <;> rfl

theorem scan_step (outerLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol)
    (remainingRev crossed : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine gapCell).stepConfig
        (restagedScanConfig outerLeft
          (current :: remainingRev) crossed) =
      some (restagedScanConfig outerLeft remainingRev
        (current :: crossed)) := by
  cases remainingRev <;> rfl

theorem scan_finish (outerLeft : List (Option MachineCodeSymbol))
    (crossed : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine gapCell).stepConfig
        (restagedScanConfig outerLeft [] crossed) =
      some (restagedGateConfig outerLeft crossed) := by
  cases crossed <;> rfl

theorem scan_run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (remainingRev crossed : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine gapCell).runConfigExact?
        (remainingRev.length + 1)
        (restagedScanConfig outerLeft remainingRev crossed) =
      some (restagedGateConfig outerLeft
        (List.append remainingRev.reverse crossed)) := by
  induction remainingRev generalizing crossed with
  | nil =>
      rw [TuringMachine.runConfigExact?]
      exact scan_finish outerLeft crossed
  | cons current remainingRev ih =>
      change (DeleteRestagedMachine.machine gapCell).runConfigExact?
          ((remainingRev.length + 1) + 1)
          (restagedScanConfig outerLeft
            (current :: remainingRev) crossed) = _
      rw [TuringMachine.runConfigExact?]
      rw [scan_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

def rewindSteps (wordRev : Word MachineCodeSymbol) : Nat :=
  2 + (wordRev.length + 1)

theorem rewind_run_exact (outerLeft : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine gapCell).runConfigExact?
        (rewindSteps (first :: rest))
        (restagedExitConfig outerLeft (first :: rest)) =
      some (restagedGateConfig outerLeft (first :: rest).reverse) := by
  unfold rewindSteps
  rw [TuringMachine.runConfigExact?_add]
  rw [skip_run_exact]
  simp only
  simpa using scan_run_exact outerLeft (first :: rest) []

def innerRunSteps (leftRev body : Word MachineCodeSymbol) : Nat :=
  rawGapSteps body +
    rewindSteps (List.append body.reverse leftRev)

theorem inner_run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol) (leftRest body : Word MachineCodeSymbol) :
    (DeleteRestagedMachine.machine gapCell).runConfigExact?
        (innerRunSteps (first :: leftRest) body)
        (gapSource outerLeft (first :: leftRest) body) =
      some (restagedGateConfig outerLeft
        (List.append (first :: leftRest).reverse body)) := by
  let outputRev := List.append body.reverse (first :: leftRest)
  have houtput : outputRev ≠ [] := by
    simp [outputRev]
  cases hout : outputRev with
  | nil => contradiction
  | cons outputFirst outputRest =>
      have hword :
          (outputFirst :: outputRest).reverse =
            List.append (first :: leftRest).reverse body := by
        rw [← hout]
        simp [outputRev, List.reverse_append, List.append_assoc]
      unfold innerRunSteps
      rw [TuringMachine.runConfigExact?_add]
      rw [editGap_run_exact]
      simp only
      have hout' :
          List.append body.reverse (first :: leftRest) =
            outputFirst :: outputRest := by
        simpa [outputRev] using hout
      rw [hout']
      rw [rewind_run_exact]
      simp [hword]

theorem compact_run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol) (leftRest body : Word MachineCodeSymbol) :
    StageInput.TwoBlankCompactor.machine.runConfigExact?
        (innerRunSteps (first :: leftRest) body)
        (compactConfig (gapSource outerLeft (first :: leftRest) body)) =
      some (compactConfig (restagedGateConfig outerLeft
        (List.append (first :: leftRest).reverse body))) := by
  apply TuringMachine.PhaseEmbedding.runConfigExact?_lift_of_eq_some
    StageInput.TwoBlankCompactor.Control.compact
    StageInput.TwoBlankCompactor.compact_step
  exact inner_run_exact outerLeft first leftRest body

theorem seek_step (outerLeft : List (Option MachineCodeSymbol))
    (current : MachineCodeSymbol)
    (remaining crossed body : Word MachineCodeSymbol) :
    StageInput.TwoBlankCompactor.machine.stepConfig
        (seekConfig outerLeft (current :: remaining) crossed body) =
      some (seekConfig outerLeft remaining (current :: crossed) body) := by
  cases remaining <;> cases body <;> rfl

theorem seek_run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (remaining crossed body : Word MachineCodeSymbol) :
    StageInput.TwoBlankCompactor.machine.runConfigExact? remaining.length
        (seekConfig outerLeft remaining crossed body) =
      some (seekConfig outerLeft []
        (List.append remaining.reverse crossed) body) := by
  induction remaining generalizing crossed with
  | nil => rfl
  | cons current remaining ih =>
      change StageInput.TwoBlankCompactor.machine.runConfigExact?
          (remaining.length + 1)
          (seekConfig outerLeft (current :: remaining) crossed body) = _
      rw [TuringMachine.runConfigExact?]
      rw [seek_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

theorem handoff_run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol) (leftRest body : Word MachineCodeSymbol) :
    StageInput.TwoBlankCompactor.machine.runConfigExact? 2
        (seekConfig outerLeft [] (first :: leftRest) body) =
      some (compactConfig
        (gapSource outerLeft (first :: leftRest) body)) := by
  cases leftRest <;> cases body <;> rfl

theorem handoff_run_exact_of_ne_nil
    (outerLeft : List (Option MachineCodeSymbol))
    (leftRev body : Word MachineCodeSymbol)
    (hnonempty : leftRev ≠ []) :
    StageInput.TwoBlankCompactor.machine.runConfigExact? 2
        (seekConfig outerLeft [] leftRev body) =
      some (compactConfig (gapSource outerLeft leftRev body)) := by
  cases leftRev with
  | nil => contradiction
  | cons first leftRest =>
      exact handoff_run_exact outerLeft first leftRest body

theorem compact_run_exact_of_ne_nil
    (outerLeft : List (Option MachineCodeSymbol))
    (leftRev body : Word MachineCodeSymbol)
    (hnonempty : leftRev ≠ []) :
    StageInput.TwoBlankCompactor.machine.runConfigExact?
        (innerRunSteps leftRev body)
        (compactConfig (gapSource outerLeft leftRev body)) =
      some (compactConfig (restagedGateConfig outerLeft
        (List.append leftRev.reverse body))) := by
  cases leftRev with
  | nil => contradiction
  | cons first leftRest =>
      exact compact_run_exact outerLeft first leftRest body

def runSteps (fuelWord body : Word MachineCodeSymbol) : Nat :=
  fuelWord.length + 2 +
    innerRunSteps
      (List.append fuelWord.reverse [MachineCodeSymbol.header]) body

theorem run_exact
    (outerLeft : List (Option MachineCodeSymbol))
    (fuelWord body : Word MachineCodeSymbol) :
    StageInput.TwoBlankCompactor.machine.runConfigExact?
        (runSteps fuelWord body)
        (seekConfig outerLeft fuelWord [MachineCodeSymbol.header] body) =
      some (compactConfig (restagedGateConfig outerLeft
        (MachineCodeSymbol.header :: List.append fuelWord body))) := by
  let leftRev :=
    List.append fuelWord.reverse [MachineCodeSymbol.header]
  have hleft : leftRev ≠ [] := by
    simp [leftRev]
  have hseek :=
    seek_run_exact outerLeft fuelWord [MachineCodeSymbol.header] body
  have hhandoff :=
    handoff_run_exact_of_ne_nil outerLeft leftRev body hleft
  have hcompact :=
    compact_run_exact_of_ne_nil outerLeft leftRev body hleft
  unfold runSteps
  rw [show fuelWord.length + 2 + innerRunSteps leftRev body =
      fuelWord.length + (2 + innerRunSteps leftRev body) by lia]
  rw [TuringMachine.runConfigExact?_add]
  rw [hseek]
  simp only
  change StageInput.TwoBlankCompactor.machine.runConfigExact?
      (2 + innerRunSteps leftRev body)
      (seekConfig outerLeft [] leftRev body) = _
  rw [TuringMachine.runConfigExact?_add]
  rw [hhandoff]
  simp only
  rw [hcompact]
  simp [leftRev, List.reverse_append]

def packedTargetTape
    (outerLeft : List (Option MachineCodeSymbol))
    (word : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match word with
  | [] =>
      { left := none :: outerLeft
        head := none
        right := [] }
  | first :: rest =>
      { left := none :: outerLeft
        head := some first
        right := rest.map some }

theorem gateTape_equiv_packedTargetTape
    (outerLeft : List (Option MachineCodeSymbol))
    (word : Word MachineCodeSymbol) :
    Tape.Equiv (gateTape outerLeft word)
      (packedTargetTape outerLeft word) := by
  cases word with
  | nil =>
      simp [gateTape, packedTargetTape, gapCell,
        StageInput.TwoBlankCompactor.gapCell,
        DeleteEndpointRewind.trailingCells,
        optionalCodeSymbolTag, codeSymbolTag,
        Tape.Equiv, Tape.dropTrailingNone]
  | cons first rest =>
      refine ⟨rfl, rfl, ?_⟩
      change Tape.dropTrailingNone
          (List.append (rest.map some) [none, none, none]) =
        Tape.dropTrailingNone (rest.map some)
      simpa using
        (FoC.Computability.dropTrailingNone_append_replicate_none
          (rest.map some) 3)

theorem run_to_packed_target
    (outerLeft : List (Option MachineCodeSymbol))
    (fuelWord body : Word MachineCodeSymbol) :
    exists endpoint : TuringMachine.Configuration MachineCodeSymbol
        StageInput.TwoBlankCompactor.Control,
      StageInput.TwoBlankCompactor.machine.runConfigExact?
          (runSteps fuelWord body)
          (seekConfig outerLeft fuelWord [MachineCodeSymbol.header] body) =
        some endpoint ∧
      endpoint.state = StageInput.TwoBlankCompactor.machine.halt ∧
      Tape.Equiv endpoint.tape
        (packedTargetTape outerLeft
          (MachineCodeSymbol.header :: List.append fuelWord body)) := by
  let target := compactConfig (restagedGateConfig outerLeft
    (MachineCodeSymbol.header :: List.append fuelWord body))
  refine ⟨target, run_exact outerLeft fuelWord body, rfl, ?_⟩
  exact gateTape_equiv_packedTargetTape outerLeft
    (MachineCodeSymbol.header :: List.append fuelWord body)

abbrev nonemptyBody {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  StageInput.TwoBlankCompactor.materializerBody right headSymbol rest

def nonemptyCleanSourceConfig {rightCount : Nat}
    (outerLeft : List (Option MachineCodeSymbol))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control :=
  seekConfig outerLeft (MachineDescription.encodeNat rightFuel)
    [MachineCodeSymbol.header] (nonemptyBody right headSymbol rest)

def nonemptyPaddedSourceTape {rightCount : Nat}
    (outerLeft : List (Option MachineCodeSymbol))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (rightFuel : Nat) : Tape MachineCodeSymbol :=
  let clean :=
    (nonemptyCleanSourceConfig outerLeft right headSymbol rest rightFuel).tape
  { clean with right := List.append clean.right [none] }

def nonemptyPaddedSourceConfig {rightCount : Nat}
    (outerLeft : List (Option MachineCodeSymbol))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (rightFuel : Nat) :
    TuringMachine.Configuration MachineCodeSymbol
      StageInput.TwoBlankCompactor.Control :=
  StageInput.TwoBlankCompactor.config .seek
    (nonemptyPaddedSourceTape outerLeft right headSymbol rest rightFuel)

theorem nonemptyCleanSource_equiv_paddedSource {rightCount : Nat}
    (outerLeft : List (Option MachineCodeSymbol))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (rightFuel : Nat) :
    Tape.Equiv
      (nonemptyCleanSourceConfig outerLeft right headSymbol rest rightFuel).tape
      (nonemptyPaddedSourceTape
        outerLeft right headSymbol rest rightFuel) := by
  refine ⟨rfl, rfl, ?_⟩
  change Tape.dropTrailingNone _ =
    Tape.dropTrailingNone (List.append _ [none])
  exact (FoC.Computability.dropTrailingNone_append_none _).symm

theorem packedWord_eq_pairCallerData {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (rightFuel : Nat) :
    MachineCodeSymbol.header ::
        List.append (MachineDescription.encodeNat rightFuel)
          (nonemptyBody right headSymbol rest) =
      ProductInput.pairCallerData right (headSymbol :: rest) rightFuel := by
  simpa [ProductInput.pairCallerData] using
    StageInput.TwoBlankCompactor.outputWord_eq_protectedWord
      right rightFuel headSymbol rest

def nonemptyRunSteps {rightCount : Nat}
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (rightFuel : Nat) : Nat :=
  runSteps (MachineDescription.encodeNat rightFuel)
    (nonemptyBody right headSymbol rest)

theorem run_nonempty_from_padded_source {rightCount : Nat}
    (outerLeft : List (Option MachineCodeSymbol))
    (right : TuringMachine MachineCodeSymbol (Fin rightCount))
    (headSymbol : MachineCodeSymbol) (rest : Word MachineCodeSymbol)
    (rightFuel : Nat) :
    exists endpoint : TuringMachine.Configuration MachineCodeSymbol
        StageInput.TwoBlankCompactor.Control,
      StageInput.TwoBlankCompactor.machine.runConfigExact?
          (nonemptyRunSteps right headSymbol rest rightFuel)
          (nonemptyPaddedSourceConfig
            outerLeft right headSymbol rest rightFuel) =
        some endpoint ∧
      endpoint.state = StageInput.TwoBlankCompactor.machine.halt ∧
      Tape.Equiv endpoint.tape
        (packedTargetTape outerLeft
          (ProductInput.pairCallerData
            right (headSymbol :: rest) rightFuel)) := by
  let fuelWord := MachineDescription.encodeNat rightFuel
  let body := nonemptyBody right headSymbol rest
  let cleanTarget := compactConfig (restagedGateConfig outerLeft
    (MachineCodeSymbol.header :: List.append fuelWord body))
  have hclean :
      StageInput.TwoBlankCompactor.machine.runConfigExact?
          (runSteps fuelWord body)
          (nonemptyCleanSourceConfig
            outerLeft right headSymbol rest rightFuel) =
        some cleanTarget := by
    exact run_exact outerLeft fuelWord body
  rcases
      TuringMachine.TapeEquivTransport.runConfigExact?_some_of_tape_equiv
        hclean
        (nonemptyCleanSource_equiv_paddedSource
          outerLeft right headSymbol rest rightFuel) with
    ⟨endpoint, hrun, hstate, htape⟩
  refine ⟨endpoint, ?_, hstate, ?_⟩
  · simpa [nonemptyRunSteps, fuelWord, body,
      nonemptyCleanSourceConfig, nonemptyPaddedSourceConfig,
      seekConfig, StageInput.TwoBlankCompactor.config] using hrun
  · refine Tape.Equiv.trans (Tape.Equiv.symm htape) ?_
    rw [← packedWord_eq_pairCallerData right headSymbol rest rightFuel]
    exact gateTape_equiv_packedTargetTape outerLeft
      (MachineCodeSymbol.header :: List.append fuelWord body)

end Pack
end ProductCleanup
end StrictProbe
end ExactFuel
end FiniteRecognizer

end Computability
end FoC

