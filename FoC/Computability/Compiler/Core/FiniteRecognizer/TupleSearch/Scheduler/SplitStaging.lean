import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.SplitLayout
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.Duplicator
import FoC.Computability.Compiler.Core.FiniteRecognizer.Product.FixedGapExpander
import FoC.Computability.Compiler.Core.FiniteRecognizer.TupleSearch.Scheduler.CandidateMaterializer

set_option doc.verso true

/-!
**Candidate-probe staging.** This bridge runs from the split scheduler layout
to the exact-fuel candidate probe.  The split layout has a positional
{lit}`moveLeft` token before the candidate; no scheduler-prefix field can
contain that token.
-/

namespace FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.SplitStaging

open Languages
open ExactFuel.StrictProbe
open ExactFuel.StrictProbe.SerializedFieldComposer
open Scheduler.CandidateMaterializer

abbrev Frame := Scheduler.Layout.Frame

def prefixAppend (frame : Frame) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    Scheduler.Layout.encodeGeometryAppend frame.geometry
      (MachineDescription.encodeNatAppend frame.cursor.round
        (Scheduler.SplitLayout.encodeSplitAppend
          frame.cursor.selectedFuel
          (frame.cursor.round - frame.cursor.selectedFuel)
          (Scheduler.SplitLayout.encodeSplitAppend frame.cursor.outer
            (frame.geometry.pairBound frame.cursor.round - frame.cursor.outer)
            (Scheduler.SplitLayout.encodeSplitAppend frame.cursor.inner
              (frame.geometry.pairBound frame.cursor.round - frame.cursor.inner)
              suffix))))

def prefixWord (frame : Frame) : Word MachineCodeSymbol :=
  prefixAppend frame []

theorem encode_eq_prefix_candidate (frame : Frame) :
    Scheduler.SplitLayout.encode frame =
      List.append (prefixWord frame)
        (Scheduler.SplitLayout.candidateMarker ::
          Scheduler.SplitLayout.candidateWord frame) := by
  cases frame with
  | mk geometry cursor input =>
      cases geometry <;> cases cursor <;>
        simp [Scheduler.SplitLayout.encode, prefixWord, prefixAppend,
          Scheduler.SplitLayout.encodeSplitAppend,
          Scheduler.Layout.encodeGeometryAppend,
          MachineDescription.encodeNatAppend, List.append_assoc]

@[simp] theorem moveLeft_not_mem_encodeNat (n : Nat) :
    ¬ List.Mem MachineCodeSymbol.moveLeft
      (MachineDescription.encodeNat n) := by
  induction n with
  | zero =>
      simp only [MachineDescription.encodeNat]
      intro hmem
      cases hmem with
      | tail _ hnil => cases hnil
  | succ n ih =>
      simp only [MachineDescription.encodeNat]
      intro hmem
      cases hmem with
      | tail _ htail => exact ih htail

theorem candidateMarker_not_mem_prefix (frame : Frame) :
    Scheduler.SplitLayout.candidateMarker ∉
      (show List MachineCodeSymbol from prefixWord frame) := by
  cases frame with
  | mk geometry cursor input =>
      cases cursor with
      | mk round inner outer selectedFuel =>
          cases geometry with
          | unbounded =>
              simp [prefixWord, prefixAppend,
                Scheduler.Layout.encodeGeometryAppend,
                Scheduler.SplitLayout.encodeSplitAppend,
                Scheduler.SplitLayout.candidateMarker,
                Scheduler.SplitLayout.splitMarker,
                MachineDescription.encodeNatAppend]
              exact ⟨moveLeft_not_mem_encodeNat round,
                moveLeft_not_mem_encodeNat selectedFuel,
                moveLeft_not_mem_encodeNat (round - selectedFuel),
                moveLeft_not_mem_encodeNat outer,
                moveLeft_not_mem_encodeNat
                  (Scheduler.Layout.Geometry.unbounded.pairBound round - outer),
                moveLeft_not_mem_encodeNat inner,
                moveLeft_not_mem_encodeNat
                  (Scheduler.Layout.Geometry.unbounded.pairBound round - inner)⟩
          | bounded budget =>
              simp [prefixWord, prefixAppend,
                Scheduler.Layout.encodeGeometryAppend,
                Scheduler.SplitLayout.encodeSplitAppend,
                Scheduler.SplitLayout.candidateMarker,
                Scheduler.SplitLayout.splitMarker,
                MachineDescription.encodeNatAppend]
              exact ⟨moveLeft_not_mem_encodeNat budget,
                moveLeft_not_mem_encodeNat round,
                moveLeft_not_mem_encodeNat selectedFuel,
                moveLeft_not_mem_encodeNat (round - selectedFuel),
                moveLeft_not_mem_encodeNat outer,
                moveLeft_not_mem_encodeNat
                  ((Scheduler.Layout.Geometry.bounded budget).pairBound round - outer),
                moveLeft_not_mem_encodeNat inner,
                moveLeft_not_mem_encodeNat
                  ((Scheduler.Layout.Geometry.bounded budget).pairBound round - inner)⟩

theorem encode_ne_nil (frame : Frame) :
    Scheduler.SplitLayout.encode frame ≠ [] := by
  simp [Scheduler.SplitLayout.encode]

inductive Control where
  | crossSeparator
  | crossOriginal
  | seekOuter
  | erasePrefix
  | seekSeparator
  | halt
deriving DecidableEq

namespace Control

def finite : Foundation.FiniteType Control where
  elems := [.crossSeparator, .crossOriginal, .seekOuter, .erasePrefix,
    .seekSeparator, .halt]
  complete := by
    intro control
    cases control <;> simp

end Control

def transition :
    Control -> Option MachineCodeSymbol ->
      Option (Option MachineCodeSymbol × Direction × Control)
  | .crossSeparator, read =>
      some (read, Direction.left, .crossOriginal)
  | .crossOriginal, read =>
      some (read, Direction.left, .seekOuter)
  | .seekOuter, some current =>
      some (some current, Direction.left, .seekOuter)
  | .seekOuter, none =>
      some (none, Direction.right, .erasePrefix)
  | .erasePrefix, some .moveLeft =>
      some (none, Direction.right, .seekSeparator)
  | .erasePrefix, some _ =>
      some (none, Direction.right, .erasePrefix)
  | .seekSeparator, some current =>
      some (some current, Direction.right, .seekSeparator)
  | .seekSeparator, none =>
      some (none, Direction.right, .halt)
  | _, _ => none

def machine : TuringMachine MachineCodeSymbol Control where
  start := .crossSeparator
  halt := .halt
  transition := transition
  statesFinite := Control.finite

def config (state : Control) (tape : Tape MachineCodeSymbol) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  { state := state, tape := tape }

def duplicatedSource (frame : Frame) :
    TuringMachine.Configuration MachineCodeSymbol Control :=
  config .crossSeparator
    (ProductDuplicator.haltTape []
      (Scheduler.SplitLayout.encode frame))

def separatorTape (word : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  { left := word.reverse.map some
    head := none
    right := word.map some }

def backwardTape (remainingRev crossed callerData :
    Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match remainingRev with
  | [] =>
      { left := []
        head := none
        right := List.append (crossed.map some)
          (none :: callerData.map some) }
  | current :: rest =>
      { left := rest.map some
        head := some current
        right := List.append (crossed.map some)
          (none :: callerData.map some) }

def cursorTape (left : List (Option MachineCodeSymbol))
    (rest callerData : Word MachineCodeSymbol) : Tape MachineCodeSymbol :=
  match rest with
  | [] =>
      { left := left
        head := none
        right := callerData.map some }
  | current :: tail =>
      { left := left
        head := some current
        right := List.append (tail.map some)
          (none :: callerData.map some) }

theorem write_head_eq_self (tape : Tape MachineCodeSymbol) :
    Tape.write tape.head tape = tape := by
  cases tape
  rfl

theorem move_left_separatorTape (word : Word MachineCodeSymbol)
    (hne : word ≠ []) :
    Tape.move Direction.left (separatorTape word) =
      backwardTape word.reverse [] word := by
  cases hrev : word.reverse with
  | nil =>
      have : word = [] := by
        rw [← List.reverse_reverse word, hrev]
        rfl
      contradiction
  | cons current rest =>
      simp [separatorTape, backwardTape, Tape.move, Tape.moveLeft, hrev]

theorem cross_separator_step (frame : Frame) :
    machine.stepConfig (duplicatedSource frame) =
      some (config .crossOriginal
        (separatorTape (Scheduler.SplitLayout.encode frame))) := by
  simp [machine, TuringMachine.stepConfig, duplicatedSource, config,
    transition, ProductDuplicator.haltTape, ProductDuplicator.scanTape,
    ProductDuplicator.tapeAtCells, separatorTape,
    Scheduler.SplitLayout.encode]
  rw [Tape.write_read_eq_self]
  exact Tape.move_left_move_right_eq_self_of_right_cons _ rfl

theorem cross_original_step (frame : Frame) :
    machine.stepConfig
        (config .crossOriginal
          (separatorTape (Scheduler.SplitLayout.encode frame))) =
      some (config .seekOuter
        (backwardTape (Scheduler.SplitLayout.encode frame).reverse []
          (Scheduler.SplitLayout.encode frame))) := by
  simp [machine, TuringMachine.stepConfig, config, transition,
    Tape.read, write_head_eq_self,
    move_left_separatorTape _ (encode_ne_nil frame)]

theorem seek_outer_step (current : MachineCodeSymbol)
    (restRev crossed callerData : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekOuter
          (backwardTape (current :: restRev) crossed callerData)) =
      some (config .seekOuter
        (backwardTape restRev (current :: crossed) callerData)) := by
  cases restRev <;> cases crossed <;> cases callerData <;> rfl

theorem seek_outer_run_exact
    (remainingRev crossed callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? remainingRev.length
        (config .seekOuter
          (backwardTape remainingRev crossed callerData)) =
      some (config .seekOuter
        (backwardTape []
          (List.append remainingRev.reverse crossed) callerData)) := by
  induction remainingRev generalizing crossed with
  | nil => rfl
  | cons current rest ih =>
      change machine.runConfigExact? (rest.length + 1)
          (config .seekOuter
            (backwardTape (current :: rest) crossed callerData)) = _
      rw [TuringMachine.runConfigExact?]
      rw [seek_outer_step]
      simp only
      rw [ih (current :: crossed)]
      simp [List.reverse_cons, List.append_assoc]

theorem seek_outer_blank_step
    (first : MachineCodeSymbol) (rest callerData : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekOuter
          (backwardTape [] (first :: rest) callerData)) =
      some (config .erasePrefix
        (cursorTape [none] (first :: rest) callerData)) := by
  cases rest <;> cases callerData <;> rfl

theorem seek_outer_blank_run_exact
    (word callerData : Word MachineCodeSymbol) (hne : word ≠ []) :
    machine.runConfigExact? 1
        (config .seekOuter (backwardTape [] word callerData)) =
      some (config .erasePrefix
        (cursorTape [none] word callerData)) := by
  cases word with
  | nil => contradiction
  | cons first rest =>
      rw [TuringMachine.runConfigExact?]
      rw [seek_outer_blank_step]
      rfl

theorem seek_original_to_prefix_run_exact (frame : Frame) :
    machine.runConfigExact?
        ((Scheduler.SplitLayout.encode frame).length + 1)
        (config .seekOuter
          (backwardTape
            (Scheduler.SplitLayout.encode frame).reverse []
            (Scheduler.SplitLayout.encode frame))) =
      some (config .erasePrefix
        (cursorTape [none] (Scheduler.SplitLayout.encode frame)
          (Scheduler.SplitLayout.encode frame))) := by
  rw [show (Scheduler.SplitLayout.encode frame).length + 1 =
      (Scheduler.SplitLayout.encode frame).reverse.length + 1 by simp]
  rw [InitialMaterializer.ExactRun.append]
  rw [seek_outer_run_exact]
  simp only [List.reverse_reverse]
  simpa using seek_outer_blank_run_exact
    (Scheduler.SplitLayout.encode frame)
    (Scheduler.SplitLayout.encode frame) (encode_ne_nil frame)

def padLeft (count : Nat)
    (left : List (Option MachineCodeSymbol)) :
    List (Option MachineCodeSymbol) :=
  List.append (List.replicate count none) left

theorem padLeft_succ_right (count : Nat)
    (left : List (Option MachineCodeSymbol)) :
    padLeft count (none :: left) = padLeft (count + 1) left := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change none :: padLeft count (none :: left) =
        none :: padLeft (count + 1) left
      exact congrArg (List.cons none) ih

theorem run_one_of_step
    {source target : TuringMachine.Configuration MachineCodeSymbol Control}
    (hstep : machine.stepConfig source = some target) :
    machine.runConfigExact? 1 source = some target := by
  rw [TuringMachine.runConfigExact?, hstep]
  rfl

theorem exactRun_trans
    {first second : Nat}
    {source middle target :
      TuringMachine.Configuration MachineCodeSymbol Control}
    (hfirst : machine.runConfigExact? first source = some middle)
    (hsecond : machine.runConfigExact? second middle = some target) :
    machine.runConfigExact? (first + second) source = some target := by
  rw [InitialMaterializer.ExactRun.append, hfirst]
  exact hsecond

theorem erase_prefix_symbol_step
    (current : MachineCodeSymbol)
    (hcurrent : current ≠ Scheduler.SplitLayout.candidateMarker)
    (left : List (Option MachineCodeSymbol))
    (rest callerData : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .erasePrefix
          (cursorTape left (current :: rest) callerData)) =
      some (config .erasePrefix
        (cursorTape (none :: left) rest callerData)) := by
  cases current <;> cases rest <;> cases callerData <;>
    simp_all [machine, TuringMachine.stepConfig, config, transition,
      cursorTape, Scheduler.SplitLayout.candidateMarker,
      Tape.read, Tape.write, Tape.move, Tape.moveRight]

theorem erase_candidate_marker_step
    (left : List (Option MachineCodeSymbol))
    (candidate callerData : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .erasePrefix
          (cursorTape left
            (Scheduler.SplitLayout.candidateMarker :: candidate)
            callerData)) =
      some (config .seekSeparator
        (cursorTape (none :: left) candidate callerData)) := by
  cases candidate <;> cases callerData <;> rfl

theorem erase_prefix_to_candidate_run_exact
    (prefixCells candidate callerData : Word MachineCodeSymbol)
    (left : List (Option MachineCodeSymbol))
    (hmarker : Scheduler.SplitLayout.candidateMarker ∉
      (show List MachineCodeSymbol from prefixCells)) :
    machine.runConfigExact? (prefixCells.length + 1)
        (config .erasePrefix
          (cursorTape left
            (List.append (show List MachineCodeSymbol from prefixCells)
              (Scheduler.SplitLayout.candidateMarker ::
                (show List MachineCodeSymbol from candidate)))
            callerData)) =
      some (config .seekSeparator
        (cursorTape (padLeft (prefixCells.length + 1) left)
          candidate callerData)) := by
  induction prefixCells generalizing left with
  | nil =>
      simpa [padLeft] using run_one_of_step
        (erase_candidate_marker_step left candidate callerData)
  | cons current rest ih =>
      have hcurrent :
          current ≠ Scheduler.SplitLayout.candidateMarker := by
        intro heq
        apply hmarker
        simp [heq]
      have hrest : Scheduler.SplitLayout.candidateMarker ∉
          (show List MachineCodeSymbol from rest) := by
        intro hmem
        apply hmarker
        simp [hmem]
      change machine.runConfigExact? ((rest.length + 1) + 1)
          (config .erasePrefix
            (cursorTape left
              (current :: List.append rest
                (Scheduler.SplitLayout.candidateMarker :: candidate))
              callerData)) = _
      rw [TuringMachine.runConfigExact?]
      rw [erase_prefix_symbol_step current hcurrent]
      simp only
      rw [ih (none :: left) hrest]
      rw [padLeft_succ_right]
      rfl

def erasedPrefixLeft (frame : Frame) :
    List (Option MachineCodeSymbol) :=
  padLeft ((prefixWord frame).length + 1) [none]

theorem erase_frame_prefix_run_exact (frame : Frame) :
    machine.runConfigExact? ((prefixWord frame).length + 1)
        (config .erasePrefix
          (cursorTape [none] (Scheduler.SplitLayout.encode frame)
            (Scheduler.SplitLayout.encode frame))) =
      some (config .seekSeparator
        (cursorTape (erasedPrefixLeft frame)
          (Scheduler.SplitLayout.candidateWord frame)
          (Scheduler.SplitLayout.encode frame))) := by
  simpa [erasedPrefixLeft, encode_eq_prefix_candidate] using
    (erase_prefix_to_candidate_run_exact
      (prefixWord frame) (Scheduler.SplitLayout.candidateWord frame)
      (Scheduler.SplitLayout.encode frame) [none]
      (candidateMarker_not_mem_prefix frame))

def erasedPackedTape (frame : Frame) : Tape MachineCodeSymbol :=
  { left := none :: List.append
      ((Scheduler.SplitLayout.candidateWord frame).reverse.map some)
      (erasedPrefixLeft frame)
    head := some MachineCodeSymbol.header
    right := (Scheduler.SplitLayout.encode frame).tail.map some }

theorem seek_separator_symbol_step (current : MachineCodeSymbol)
    (left : List (Option MachineCodeSymbol))
    (rest callerData : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekSeparator
          (cursorTape left (current :: rest) callerData)) =
      some (config .seekSeparator
        (cursorTape (some current :: left) rest callerData)) := by
  cases rest <;> cases callerData <;> rfl

theorem seek_separator_scan_run_exact
    (remaining : Word MachineCodeSymbol)
    (left : List (Option MachineCodeSymbol))
    (callerData : Word MachineCodeSymbol) :
    machine.runConfigExact? remaining.length
        (config .seekSeparator
          (cursorTape left remaining callerData)) =
      some (config .seekSeparator
        (cursorTape
          (List.append (remaining.reverse.map some) left)
          [] callerData)) := by
  induction remaining generalizing left with
  | nil => rfl
  | cons current rest ih =>
      change machine.runConfigExact? (rest.length + 1)
          (config .seekSeparator
            (cursorTape left (current :: rest) callerData)) = _
      rw [TuringMachine.runConfigExact?]
      rw [seek_separator_symbol_step]
      simp only
      rw [ih (some current :: left)]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem seek_separator_blank_step
    (left : List (Option MachineCodeSymbol))
    (first : MachineCodeSymbol) (rest : Word MachineCodeSymbol) :
    machine.stepConfig
        (config .seekSeparator
          (cursorTape left [] (first :: rest))) =
      some (config .halt
        { left := none :: left
          head := some first
          right := rest.map some }) := by
  cases rest <;> cases left <;> rfl

theorem seek_candidate_to_packed_run_exact (frame : Frame) :
    machine.runConfigExact?
        ((Scheduler.SplitLayout.candidateWord frame).length + 1)
        (config .seekSeparator
          (cursorTape (erasedPrefixLeft frame)
            (Scheduler.SplitLayout.candidateWord frame)
            (Scheduler.SplitLayout.encode frame))) =
      some (config .halt (erasedPackedTape frame)) := by
  rw [InitialMaterializer.ExactRun.append]
  rw [seek_separator_scan_run_exact]
  simp only
  rw [TuringMachine.runConfigExact?]
  have hblank := seek_separator_blank_step
    (List.append
      ((Scheduler.SplitLayout.candidateWord frame).reverse.map some)
      (erasedPrefixLeft frame))
    MachineCodeSymbol.header
    (Scheduler.SplitLayout.encode frame).tail
  have hblank' :
      machine.stepConfig
          (config .seekSeparator
            (cursorTape
              (List.append
                ((Scheduler.SplitLayout.candidateWord frame).reverse.map
                  some)
                (erasedPrefixLeft frame)) []
              (Scheduler.SplitLayout.encode frame))) =
        some (config .halt (erasedPackedTape frame)) := by
    simpa [Scheduler.SplitLayout.encode, erasedPackedTape] using hblank
  rw [hblank']
  rfl

theorem duplicate_endpoint_to_packed_run_exact (frame : Frame) :
    exists steps : Nat,
      machine.runConfigExact? steps (duplicatedSource frame) =
        some (config .halt (erasedPackedTape frame)) := by
  have hcross0 := run_one_of_step (cross_separator_step frame)
  have hcross1 := run_one_of_step (cross_original_step frame)
  have hseek := seek_original_to_prefix_run_exact frame
  have herase := erase_frame_prefix_run_exact frame
  have hcandidate := seek_candidate_to_packed_run_exact frame
  have h01 := exactRun_trans hcross0 hcross1
  have h012 := exactRun_trans h01 hseek
  have h0123 := exactRun_trans h012 herase
  have hfull := exactRun_trans h0123 hcandidate
  exact ⟨((((1 + 1) +
      ((Scheduler.SplitLayout.encode frame).length + 1)) +
      ((prefixWord frame).length + 1)) +
      ((Scheduler.SplitLayout.candidateWord frame).length + 1)),
    hfull⟩

def erasedPaddingCount (frame : Frame) : Nat :=
  (prefixWord frame).length + 2

theorem replicate_none_append (first second : Nat) :
    List.append
        (List.replicate first (none : Option MachineCodeSymbol))
        (List.replicate second none) =
      List.replicate (first + second) none := by
  induction first with
  | zero => simp
  | succ first ih =>
      simp [List.replicate_succ, Nat.succ_add]

theorem erasedPrefixLeft_eq_replicate (frame : Frame) :
    erasedPrefixLeft frame =
      List.replicate (erasedPaddingCount frame) none := by
  simpa [erasedPrefixLeft, erasedPaddingCount, padLeft] using
    replicate_none_append ((prefixWord frame).length + 1) 1

theorem drop_word_padding
    (word : Word MachineCodeSymbol) (padding : Nat) :
    Tape.dropTrailingNone
        (List.append (word.reverse.map some)
          (List.replicate padding none)) =
      Tape.dropTrailingNone
        (List.append (word.reverse.map some) [none]) := by
  change List MachineCodeSymbol at word
  exact (FoC.Computability.dropTrailingNone_append_replicate_none
      (word.reverse.map some) padding).trans
    (FoC.Computability.dropTrailingNone_append_none
      (word.reverse.map some)).symm

theorem erasedPackedTape_equiv_packedSource (frame : Frame) :
    Tape.Equiv (erasedPackedTape frame)
      (ProductGapExpander.packedSourceConfig (gapExtra := 2)
        (Scheduler.SplitLayout.candidateWord frame)
        (Scheduler.SplitLayout.encode frame)).tape := by
  unfold erasedPackedTape ProductGapExpander.packedSourceConfig
    ProductGapExpander.config ProductGapExpander.packedSourceTape Tape.Equiv
  refine ⟨?_, rfl, rfl⟩
  apply Tape.dropTrailingNone_cons_eq rfl
  rw [erasedPrefixLeft_eq_replicate]
  exact drop_word_padding
    (Scheduler.SplitLayout.candidateWord frame)
    (erasedPaddingCount frame)

def cleanDuplicatorSource (frame : Frame) :
    TuringMachine.Configuration MachineCodeSymbol ProductDuplicator.Control :=
  { state := ProductDuplicator.machine.start
    tape := Tape.input (Scheduler.SplitLayout.encode frame) }

theorem canonicalDuplicatorSource_equiv_clean (frame : Frame) :
    Tape.Equiv
      (ProductDuplicator.sourceConfig []
        (Scheduler.SplitLayout.encode frame)).tape
      (cleanDuplicatorSource frame).tape := by
  have hcursor := ProductDuplicator.sourceTape_equiv_cursor
    ([] : Word MachineCodeSymbol) (Scheduler.SplitLayout.encode frame)
  simpa [ProductDuplicator.sourceConfig, ProductDuplicator.sourceTape,
    ProductDuplicator.scanConfig, cleanDuplicatorSource,
    ExactFuel.StrictProbe.SerializedShift.cursorTape,
    Scheduler.SplitLayout.encode, Tape.input] using hcursor

theorem duplicate_clean_run (frame : Frame) :
    exists endpoint : TuringMachine.Configuration MachineCodeSymbol
        ProductDuplicator.Control,
      ProductDuplicator.machine.runConfigExact?
          (ProductDuplicator.runSteps
            (Scheduler.SplitLayout.encode frame))
          (cleanDuplicatorSource frame) = some endpoint ∧
      endpoint.state = ProductDuplicator.machine.halt ∧
      Tape.Equiv
        (ProductDuplicator.haltConfig []
          (Scheduler.SplitLayout.encode frame)).tape endpoint.tape := by
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := ProductDuplicator.sourceConfig []
        (Scheduler.SplitLayout.encode frame))
      (padded := cleanDuplicatorSource frame)
      (cleanFinal := ProductDuplicator.haltConfig []
        (Scheduler.SplitLayout.encode frame))
      ProductDuplicator.machine
      (ProductDuplicator.runSteps
        (Scheduler.SplitLayout.encode frame))
      rfl (canonicalDuplicatorSource_equiv_clean frame)
      (ProductDuplicator.run_exact []
        (Scheduler.SplitLayout.encode frame)) with
    ⟨endpoint, hrun, hstate, htape⟩
  exact ⟨endpoint, hrun, hstate.symm, htape⟩

theorem duplicate_from_equiv_input
    (frame : Frame) (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input (Scheduler.SplitLayout.encode frame)) sourceTape) :
    exists endpoint : TuringMachine.Configuration MachineCodeSymbol
        ProductDuplicator.Control,
      ProductDuplicator.machine.runConfigExact?
          (ProductDuplicator.runSteps
            (Scheduler.SplitLayout.encode frame))
          { state := ProductDuplicator.machine.start
            tape := sourceTape } = some endpoint ∧
      endpoint.state = ProductDuplicator.machine.halt ∧
      Tape.Equiv
        (ProductDuplicator.haltConfig []
          (Scheduler.SplitLayout.encode frame)).tape endpoint.tape := by
  have hcanonicalSource : Tape.Equiv
      (ProductDuplicator.sourceConfig []
        (Scheduler.SplitLayout.encode frame)).tape sourceTape :=
    Tape.Equiv.trans (canonicalDuplicatorSource_equiv_clean frame) hsource
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := ProductDuplicator.sourceConfig []
        (Scheduler.SplitLayout.encode frame))
      (padded :=
        { state := ProductDuplicator.machine.start
          tape := sourceTape })
      (cleanFinal := ProductDuplicator.haltConfig []
        (Scheduler.SplitLayout.encode frame))
      ProductDuplicator.machine
      (ProductDuplicator.runSteps
        (Scheduler.SplitLayout.encode frame))
      rfl hcanonicalSource
      (ProductDuplicator.run_exact []
        (Scheduler.SplitLayout.encode frame)) with
    ⟨endpoint, hrun, hstate, htape⟩
  exact ⟨endpoint, hrun, hstate.symm, htape⟩

theorem erase_from_duplicate_endpoint
    (frame : Frame)
    (endpoint : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control)
    (_hstate : endpoint.state = ProductDuplicator.machine.halt)
    (htape : Tape.Equiv
      (ProductDuplicator.haltConfig []
        (Scheduler.SplitLayout.encode frame)).tape endpoint.tape) :
    exists (steps : Nat)
        (erasedEndpoint : TuringMachine.Configuration MachineCodeSymbol
          Control),
      machine.runConfigExact? steps
          (config .crossSeparator endpoint.tape) = some erasedEndpoint ∧
      erasedEndpoint.state = machine.halt ∧
      Tape.Equiv (erasedPackedTape frame) erasedEndpoint.tape := by
  rcases duplicate_endpoint_to_packed_run_exact frame with
    ⟨steps, hclean⟩
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := duplicatedSource frame)
      (padded := config .crossSeparator endpoint.tape)
      (cleanFinal := config .halt (erasedPackedTape frame))
      machine steps rfl htape hclean with
    ⟨erasedEndpoint, hrun, htargetState, htargetTape⟩
  exact ⟨steps, erasedEndpoint, hrun, htargetState.symm, htargetTape⟩

theorem candidateWord_eq_split (frame : Frame) :
    Scheduler.SplitLayout.candidateWord frame =
      MachineDescription.encodeNatAppend frame.cursor.selectedFuel
        (Scheduler.CandidateMaterializer.candidateHead frame.cursor.outer ::
          Scheduler.CandidateMaterializer.candidateRest frame.input
            frame.cursor.inner frame.cursor.outer) := by
  unfold Scheduler.SplitLayout.candidateWord
  rw [Scheduler.CandidateMaterializer.candidateHead_cons_candidateRest]

def gapTarget (frame : Frame) :
    TuringMachine.Configuration MachineCodeSymbol
      (ProductGapExpander.Control 2) :=
  ProductGapExpander.Nonempty.haltConfig (gapExtra := 2)
    (MachineDescription.encodeNat frame.cursor.selectedFuel).reverse
    (Scheduler.CandidateMaterializer.candidateHead frame.cursor.outer)
    (Scheduler.CandidateMaterializer.candidateRest frame.input
      frame.cursor.inner frame.cursor.outer)
    (Scheduler.SplitLayout.encode frame)

theorem gap_run_exact (frame : Frame) :
    (ProductGapExpander.machine (by decide : 0 < 2)).runConfigExact?
        (ProductGapExpander.Nonempty.runSteps
          frame.cursor.selectedFuel
          (Scheduler.CandidateMaterializer.candidateHead frame.cursor.outer ::
            Scheduler.CandidateMaterializer.candidateRest frame.input
              frame.cursor.inner frame.cursor.outer))
        (ProductGapExpander.packedSourceConfig (gapExtra := 2)
          (Scheduler.SplitLayout.candidateWord frame)
          (Scheduler.SplitLayout.encode frame)) =
      some (gapTarget frame) := by
  have hrun := ProductGapExpander.Nonempty.run_generic_exact
    frame.cursor.selectedFuel
    (Scheduler.CandidateMaterializer.candidateHead frame.cursor.outer)
    (Scheduler.CandidateMaterializer.candidateRest frame.input
      frame.cursor.inner frame.cursor.outer)
    (Scheduler.SplitLayout.encode frame).tail
  rw [candidateWord_eq_split]
  simpa [gapTarget, Scheduler.SplitLayout.encode] using hrun

theorem gap_from_erased_endpoint
    (frame : Frame)
    (erasedEndpoint : TuringMachine.Configuration MachineCodeSymbol Control)
    (_hstate : erasedEndpoint.state = machine.halt)
    (htape : Tape.Equiv
      (ProductGapExpander.packedSourceConfig (gapExtra := 2)
        (Scheduler.SplitLayout.candidateWord frame)
        (Scheduler.SplitLayout.encode frame)).tape
      erasedEndpoint.tape) :
    exists gapEndpoint : TuringMachine.Configuration MachineCodeSymbol
        (ProductGapExpander.Control 2),
      (ProductGapExpander.machine (by decide : 0 < 2)).runConfigExact?
          (ProductGapExpander.Nonempty.runSteps
            frame.cursor.selectedFuel
            (Scheduler.CandidateMaterializer.candidateHead frame.cursor.outer ::
              Scheduler.CandidateMaterializer.candidateRest frame.input
                frame.cursor.inner frame.cursor.outer))
          { state := (ProductGapExpander.machine
              (by decide : 0 < 2)).start
            tape := erasedEndpoint.tape } = some gapEndpoint ∧
      gapEndpoint.state =
        (ProductGapExpander.machine (by decide : 0 < 2)).halt ∧
      Tape.Equiv (gapTarget frame).tape gapEndpoint.tape := by
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := ProductGapExpander.packedSourceConfig (gapExtra := 2)
        (Scheduler.SplitLayout.candidateWord frame)
        (Scheduler.SplitLayout.encode frame))
      (padded :=
        { state := (ProductGapExpander.machine
            (by decide : 0 < 2)).start
          tape := erasedEndpoint.tape })
      (cleanFinal := gapTarget frame)
      (ProductGapExpander.machine (by decide : 0 < 2))
      (ProductGapExpander.Nonempty.runSteps
        frame.cursor.selectedFuel
        (Scheduler.CandidateMaterializer.candidateHead frame.cursor.outer ::
          Scheduler.CandidateMaterializer.candidateRest frame.input
            frame.cursor.inner frame.cursor.outer))
      rfl htape (gap_run_exact frame) with
    ⟨gapEndpoint, hrun, htargetState, htargetTape⟩
  exact ⟨gapEndpoint, hrun, htargetState.symm, htargetTape⟩

def splitTailSource {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) :
    TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.CandidateMaterializer.Control selected) :=
  Scheduler.CandidateMaterializer.materializerConfig
    (InitialMaterializer.FullMaterializerMachine.tailConfig selected
      (ProductCallerTail.NonemptyCallerTail.sourceConfig
        (MachineDescription.encodeNat frame.cursor.selectedFuel).reverse
        (Scheduler.CandidateMaterializer.candidateHead frame.cursor.outer)
        (Scheduler.CandidateMaterializer.candidateRest frame.input
          frame.cursor.inner frame.cursor.outer)
        (Scheduler.SplitLayout.encode frame)))

def splitTailHandoff {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) :
    TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.CandidateMaterializer.Control selected) :=
  Scheduler.CandidateMaterializer.materializerConfig
    (InitialMaterializer.FullMaterializerMachine.tailConfig selected
      (ProductCallerTail.NonemptyCallerTail.haltConfig
        (Scheduler.CandidateMaterializer.candidateHead frame.cursor.outer)
        (MachineDescription.encodeNat frame.cursor.selectedFuel).reverse
        (Scheduler.CandidateMaterializer.candidateRest frame.input
          frame.cursor.inner frame.cursor.outer).reverse
        (Scheduler.SplitLayout.encode frame)))

theorem split_tail_to_handoff_run_exact {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) :
    (Scheduler.CandidateMaterializer.machine selected).runConfigExact?
        ((Scheduler.CandidateMaterializer.candidateRest frame.input
          frame.cursor.inner frame.cursor.outer).length + 4)
        (splitTailSource selected frame) =
      some (splitTailHandoff selected frame) := by
  have htail := ProductCallerTail.NonemptyCallerTail.run_exact
    (MachineDescription.encodeNat frame.cursor.selectedFuel).reverse
    (Scheduler.CandidateMaterializer.candidateHead frame.cursor.outer)
    (Scheduler.CandidateMaterializer.candidateRest frame.input
      frame.cursor.inner frame.cursor.outer)
    (Scheduler.SplitLayout.encode frame)
  have hmaterializer :=
    InitialMaterializer.FullMaterializerMachine.tail_run_of_eq_some
    selected
    ((Scheduler.CandidateMaterializer.candidateRest frame.input
      frame.cursor.inner frame.cursor.outer).length + 4) _ _ htail
  exact Scheduler.CandidateMaterializer.materializer_run_lift
    selected hmaterializer

def SplitCandidateMaterializeSpec {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) : Prop :=
  exists targetTape : Tape MachineCodeSymbol,
  exists steps : Nat,
    (Scheduler.CandidateMaterializer.machine selected).runConfigExact? steps
          (splitTailSource selected frame) =
        some
          { state := (Scheduler.CandidateMaterializer.machine selected).halt
            tape := targetTape } ∧
      Tape.Equiv targetTape
        (CandidateKernel.ProbeReturn.candidateTape selected
          (Scheduler.SplitLayout.encode frame) frame.input
          frame.cursor.inner frame.cursor.outer
          frame.cursor.selectedFuel)

theorem materialize_split_candidate {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) :
    SplitCandidateMaterializeSpec selected frame := by
  have htail := split_tail_to_handoff_run_exact selected frame
  rcases Scheduler.CandidateMaterializer.materialize_candidate_from_tail
      selected (Scheduler.SplitLayout.encode frame) frame.input
      frame.cursor.inner frame.cursor.outer frame.cursor.selectedFuel with
    ⟨targetTape, finishSteps, hfinish, htape⟩
  refine ⟨targetTape,
    (Scheduler.CandidateMaterializer.candidateRest frame.input
      frame.cursor.inner frame.cursor.outer).length + 4 + finishSteps,
    ?_, htape⟩
  rw [InitialMaterializer.ExactRun.append, htail]
  exact hfinish

theorem gapTarget_tape_eq_splitTailSource
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) :
    (gapTarget frame).tape = (splitTailSource selected frame).tape := by
  rfl

theorem materialize_from_gap_endpoint
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame)
    (gapEndpoint : TuringMachine.Configuration MachineCodeSymbol
      (ProductGapExpander.Control 2))
    (_hstate : gapEndpoint.state =
      (ProductGapExpander.machine (by decide : 0 < 2)).halt)
    (htape : Tape.Equiv (gapTarget frame).tape gapEndpoint.tape) :
    exists (steps : Nat)
        (endpoint : TuringMachine.Configuration MachineCodeSymbol
          (Scheduler.CandidateMaterializer.Control selected)),
      (Scheduler.CandidateMaterializer.machine selected).runConfigExact? steps
          { state := (splitTailSource selected frame).state
            tape := gapEndpoint.tape } = some endpoint ∧
      endpoint.state =
        (Scheduler.CandidateMaterializer.machine selected).halt ∧
      Tape.Equiv endpoint.tape
        (CandidateKernel.ProbeReturn.candidateTape selected
          (Scheduler.SplitLayout.encode frame) frame.input
          frame.cursor.inner frame.cursor.outer
          frame.cursor.selectedFuel) := by
  rcases materialize_split_candidate selected frame with
    ⟨targetTape, steps, hclean, htargetTape⟩
  have hsourceTape : Tape.Equiv
      (splitTailSource selected frame).tape gapEndpoint.tape := by
    rw [← gapTarget_tape_eq_splitTailSource selected frame]
    exact htape
  rcases InitialMaterializer.TuringExactEquiv.runConfigExact?_some_of_equiv
      (clean := splitTailSource selected frame)
      (padded :=
        { state := (splitTailSource selected frame).state
          tape := gapEndpoint.tape })
      (cleanFinal :=
        { state := (Scheduler.CandidateMaterializer.machine selected).halt
          tape := targetTape })
      (Scheduler.CandidateMaterializer.machine selected) steps rfl
      hsourceTape hclean with
    ⟨endpoint, hrun, htargetState, hactualTape⟩
  exact ⟨steps, endpoint, hrun, htargetState.symm,
    Tape.Equiv.trans (Tape.Equiv.symm hactualTape) htargetTape⟩

def CandidatePhaseSpec
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) (sourceTape : Tape MachineCodeSymbol) : Prop :=
  exists
    (duplicatorEndpoint : TuringMachine.Configuration MachineCodeSymbol
      ProductDuplicator.Control)
    (eraseSteps : Nat)
    (erasedEndpoint : TuringMachine.Configuration MachineCodeSymbol Control)
    (gapEndpoint : TuringMachine.Configuration MachineCodeSymbol
      (ProductGapExpander.Control 2))
    (materializeSteps : Nat)
    (candidateEndpoint : TuringMachine.Configuration MachineCodeSymbol
      (Scheduler.CandidateMaterializer.Control selected)),
    ProductDuplicator.machine.runConfigExact?
        (ProductDuplicator.runSteps
          (Scheduler.SplitLayout.encode frame))
        { state := ProductDuplicator.machine.start
          tape := sourceTape } = some duplicatorEndpoint ∧
    duplicatorEndpoint.state = ProductDuplicator.machine.halt ∧
    machine.runConfigExact? eraseSteps
        (config .crossSeparator duplicatorEndpoint.tape) =
      some erasedEndpoint ∧
    erasedEndpoint.state = machine.halt ∧
    (ProductGapExpander.machine (by decide : 0 < 2)).runConfigExact?
        (ProductGapExpander.Nonempty.runSteps
          frame.cursor.selectedFuel
          (Scheduler.CandidateMaterializer.candidateHead frame.cursor.outer ::
            Scheduler.CandidateMaterializer.candidateRest frame.input
              frame.cursor.inner frame.cursor.outer))
        { state := (ProductGapExpander.machine
            (by decide : 0 < 2)).start
          tape := erasedEndpoint.tape } = some gapEndpoint ∧
    gapEndpoint.state =
      (ProductGapExpander.machine (by decide : 0 < 2)).halt ∧
    (Scheduler.CandidateMaterializer.machine selected).runConfigExact?
        materializeSteps
        { state := (splitTailSource selected frame).state
          tape := gapEndpoint.tape } = some candidateEndpoint ∧
    candidateEndpoint.state =
      (Scheduler.CandidateMaterializer.machine selected).halt ∧
    Tape.Equiv candidateEndpoint.tape
      (CandidateKernel.ProbeReturn.candidateTape selected
        (Scheduler.SplitLayout.encode frame) frame.input
        frame.cursor.inner frame.cursor.outer frame.cursor.selectedFuel)

theorem recovered_frame_to_candidate_phases
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) (sourceTape : Tape MachineCodeSymbol)
    (hsource : Tape.Equiv
      (Tape.input (Scheduler.SplitLayout.encode frame)) sourceTape) :
    CandidatePhaseSpec selected frame sourceTape := by
  rcases duplicate_from_equiv_input frame sourceTape hsource with
    ⟨duplicatorEndpoint, hduplicate, hduplicateState, hduplicateTape⟩
  rcases erase_from_duplicate_endpoint frame duplicatorEndpoint
      hduplicateState hduplicateTape with
    ⟨eraseSteps, erasedEndpoint, herase, heraseState, heraseTape⟩
  have hpacked : Tape.Equiv
      (ProductGapExpander.packedSourceConfig (gapExtra := 2)
        (Scheduler.SplitLayout.candidateWord frame)
        (Scheduler.SplitLayout.encode frame)).tape
      erasedEndpoint.tape :=
    Tape.Equiv.trans (Tape.Equiv.symm
      (erasedPackedTape_equiv_packedSource frame)) heraseTape
  rcases gap_from_erased_endpoint frame erasedEndpoint heraseState
      hpacked with
    ⟨gapEndpoint, hgap, hgapState, hgapTape⟩
  rcases materialize_from_gap_endpoint selected frame gapEndpoint
      hgapState hgapTape with
    ⟨materializeSteps, candidateEndpoint, hmaterialize,
      hcandidateState, hcandidateTape⟩
  exact ⟨duplicatorEndpoint, eraseSteps, erasedEndpoint,
    gapEndpoint, materializeSteps, candidateEndpoint,
    hduplicate, hduplicateState, herase, heraseState,
    hgap, hgapState, hmaterialize, hcandidateState, hcandidateTape⟩

theorem clean_frame_to_candidate_phases
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) :
    CandidatePhaseSpec selected frame
      (Tape.input (Scheduler.SplitLayout.encode frame)) := by
  exact recovered_frame_to_candidate_phases selected frame
    (Tape.input (Scheduler.SplitLayout.encode frame))
    (Tape.Equiv.refl _)

theorem recovered_gate_to_advanced_candidate
    {stateCount : Nat}
    (selected : TuringMachine MachineCodeSymbol (Fin stateCount))
    (frame : Frame) (gateTape : Tape MachineCodeSymbol)
    (hgate : Tape.Equiv gateTape
      (Tape.input
        (Scheduler.SplitLayout.encode frame.advance))) :
    CandidatePhaseSpec selected frame.advance gateTape := by
  exact recovered_frame_to_candidate_phases selected frame.advance gateTape
    (Tape.Equiv.symm hgate)

end FoC.Computability.FiniteRecognizer.TupleSearch.Scheduler.SplitStaging
