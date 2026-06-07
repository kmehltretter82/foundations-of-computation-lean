import FoC.Computability.Coding
import FoC.Computability.Encoding

set_option doc.verso true

/-!
# Concrete diagonal pair machine

This module contains the explicit finite-machine witness for the concrete
diagonal pair map used in Chapter 5, Section 5.3.

The file keeps two witnesses visible. The legacy marker machine proves the old
compatibility-level {name}`FoC.Computability.TuringComputable` statement, whose
output encoder may collapse different output symbols. The faithful copy machine
proves {name}`FoC.Computability.FaithfulTuringComputable` by preserving the
concrete pair-code alphabet through injective encodings.
-/

namespace FoC
namespace Computability

open Foundation
open Languages

def ConcretePairCodeSymbol (code : Type u) : Type u :=
  PairCodeSymbol code

def ConcreteDiagonalPairMap (w : Word code) :
    Word (ConcretePairCodeSymbol code) :=
  PairCodeSymbol.diagonalMap w

def ConcreteMachineCodeSymbol : Type :=
  MachineCodeSymbol

def ConcreteDiagonalPairMapComputable : Prop :=
  TuringComputable
    (ConcreteDiagonalPairMap :
      Word ConcreteMachineCodeSymbol ->
        Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))

def FaithfulConcreteDiagonalPairMapComputable : Prop :=
  FaithfulTuringComputable
    (ConcreteDiagonalPairMap :
      Word ConcreteMachineCodeSymbol ->
        Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))

def ConcreteMachineCodeSymbolFinite :
    Foundation.FiniteType ConcreteMachineCodeSymbol :=
  MachineCodeSymbol.finite

/-!
The machine below computes the encoded diagonal-pair word by mapping every left
tag, separator, and right tag to a single output marker. The proof is still
operational: the machine scans the input, writes one separator marker, converts
each raw input cell into an output marker, appends one marker for the matching
right component, and then halts.
-/

inductive ConcreteDiagonalPairMapMachineSymbol where
  | raw : ConcreteMachineCodeSymbol -> ConcreteDiagonalPairMapMachineSymbol
  | marker : ConcreteDiagonalPairMapMachineSymbol

namespace ConcreteDiagonalPairMapMachineSymbol

def finite : Foundation.FiniteType ConcreteDiagonalPairMapMachineSymbol where
  elems :=
    [ConcreteDiagonalPairMapMachineSymbol.marker] ++
      ConcreteMachineCodeSymbolFinite.elems.map
        ConcreteDiagonalPairMapMachineSymbol.raw
  complete := by
    intro symbol
    cases symbol with
    | raw code =>
        simp [ConcreteMachineCodeSymbolFinite.complete code]
    | marker =>
        simp

end ConcreteDiagonalPairMapMachineSymbol

inductive ConcreteDiagonalPairMapMachineState where
  | initStart
  | initScan
  | return
  | append
  | halt
deriving DecidableEq

namespace ConcreteDiagonalPairMapMachineState

def finite : Foundation.FiniteType ConcreteDiagonalPairMapMachineState where
  elems :=
    [ ConcreteDiagonalPairMapMachineState.initStart
    , ConcreteDiagonalPairMapMachineState.initScan
    , ConcreteDiagonalPairMapMachineState.return
    , ConcreteDiagonalPairMapMachineState.append
    , ConcreteDiagonalPairMapMachineState.halt
    ]
  complete := by
    intro state
    cases state <;> simp

end ConcreteDiagonalPairMapMachineState

def concreteDiagonalPairMapInputEncode
    (code : ConcreteMachineCodeSymbol) :
    ConcreteDiagonalPairMapMachineSymbol :=
  ConcreteDiagonalPairMapMachineSymbol.raw code

def concreteDiagonalPairMapOutputEncode
    (_ : ConcretePairCodeSymbol ConcreteMachineCodeSymbol) :
    ConcreteDiagonalPairMapMachineSymbol :=
  ConcreteDiagonalPairMapMachineSymbol.marker

def concreteDiagonalPairMapTransition :
    ConcreteDiagonalPairMapMachineState ->
      Option ConcreteDiagonalPairMapMachineSymbol ->
        Option
          (Option ConcreteDiagonalPairMapMachineSymbol × Direction ×
            ConcreteDiagonalPairMapMachineState)
  | ConcreteDiagonalPairMapMachineState.initStart, none =>
      some (some ConcreteDiagonalPairMapMachineSymbol.marker, Direction.right,
        ConcreteDiagonalPairMapMachineState.halt)
  | ConcreteDiagonalPairMapMachineState.initStart,
      some (ConcreteDiagonalPairMapMachineSymbol.raw code) =>
      some (some (ConcreteDiagonalPairMapMachineSymbol.raw code),
        Direction.right, ConcreteDiagonalPairMapMachineState.initScan)
  | ConcreteDiagonalPairMapMachineState.initStart,
      some ConcreteDiagonalPairMapMachineSymbol.marker =>
      some (some ConcreteDiagonalPairMapMachineSymbol.marker, Direction.right,
        ConcreteDiagonalPairMapMachineState.initScan)
  | ConcreteDiagonalPairMapMachineState.initScan, none =>
      some (some ConcreteDiagonalPairMapMachineSymbol.marker, Direction.left,
        ConcreteDiagonalPairMapMachineState.return)
  | ConcreteDiagonalPairMapMachineState.initScan,
      some (ConcreteDiagonalPairMapMachineSymbol.raw code) =>
      some (some (ConcreteDiagonalPairMapMachineSymbol.raw code),
        Direction.right, ConcreteDiagonalPairMapMachineState.initScan)
  | ConcreteDiagonalPairMapMachineState.initScan,
      some ConcreteDiagonalPairMapMachineSymbol.marker =>
      some (some ConcreteDiagonalPairMapMachineSymbol.marker, Direction.right,
        ConcreteDiagonalPairMapMachineState.initScan)
  | ConcreteDiagonalPairMapMachineState.return, none =>
      some (none, Direction.right,
        ConcreteDiagonalPairMapMachineState.halt)
  | ConcreteDiagonalPairMapMachineState.return,
      some (ConcreteDiagonalPairMapMachineSymbol.raw _) =>
      some (some ConcreteDiagonalPairMapMachineSymbol.marker, Direction.right,
        ConcreteDiagonalPairMapMachineState.append)
  | ConcreteDiagonalPairMapMachineState.return,
      some ConcreteDiagonalPairMapMachineSymbol.marker =>
      some (some ConcreteDiagonalPairMapMachineSymbol.marker, Direction.left,
        ConcreteDiagonalPairMapMachineState.return)
  | ConcreteDiagonalPairMapMachineState.append, none =>
      some (some ConcreteDiagonalPairMapMachineSymbol.marker, Direction.left,
        ConcreteDiagonalPairMapMachineState.return)
  | ConcreteDiagonalPairMapMachineState.append,
      some (ConcreteDiagonalPairMapMachineSymbol.raw code) =>
      some (some (ConcreteDiagonalPairMapMachineSymbol.raw code),
        Direction.right, ConcreteDiagonalPairMapMachineState.append)
  | ConcreteDiagonalPairMapMachineState.append,
      some ConcreteDiagonalPairMapMachineSymbol.marker =>
      some (some ConcreteDiagonalPairMapMachineSymbol.marker, Direction.right,
        ConcreteDiagonalPairMapMachineState.append)
  | ConcreteDiagonalPairMapMachineState.halt, _ =>
      none

def ConcreteDiagonalPairMapMachine :
    TuringMachine
      ConcreteDiagonalPairMapMachineSymbol
      ConcreteDiagonalPairMapMachineState where
  start := ConcreteDiagonalPairMapMachineState.initStart
  halt := ConcreteDiagonalPairMapMachineState.halt
  transition := concreteDiagonalPairMapTransition
  statesFinite := ConcreteDiagonalPairMapMachineState.finite

def concreteDiagonalPairMapRawCells
    (w : Word ConcreteMachineCodeSymbol) :
    List (Option ConcreteDiagonalPairMapMachineSymbol) :=
  w.map (fun code =>
    some (ConcreteDiagonalPairMapMachineSymbol.raw code))

def concreteDiagonalPairMapMarkerCells (n : Nat) :
    List (Option ConcreteDiagonalPairMapMachineSymbol) :=
  List.replicate n (some ConcreteDiagonalPairMapMachineSymbol.marker)

def concreteDiagonalPairMapScanTape
    (seenRev rest : Word ConcreteMachineCodeSymbol) :
    Tape ConcreteDiagonalPairMapMachineSymbol :=
  match rest with
  | [] =>
      { left := concreteDiagonalPairMapRawCells seenRev
        head := none
        right := [] }
  | code :: suffix =>
      { left := concreteDiagonalPairMapRawCells seenRev
        head := some (ConcreteDiagonalPairMapMachineSymbol.raw code)
        right := concreteDiagonalPairMapRawCells suffix }

def concreteDiagonalPairMapReturnTape
    (unprocessedRev : Word ConcreteMachineCodeSymbol) (markers : Nat) :
    Tape ConcreteDiagonalPairMapMachineSymbol :=
  match unprocessedRev with
  | [] =>
      { left := []
        head := none
        right := concreteDiagonalPairMapMarkerCells markers }
  | code :: rest =>
      { left := concreteDiagonalPairMapRawCells rest
        head := some (ConcreteDiagonalPairMapMachineSymbol.raw code)
        right := concreteDiagonalPairMapMarkerCells markers }

def concreteDiagonalPairMapAppendScanTape
    (leftRaw : Word ConcreteMachineCodeSymbol)
    (markersSeen markersRemaining : Nat) :
    Tape ConcreteDiagonalPairMapMachineSymbol :=
  match markersRemaining with
  | 0 =>
      { left :=
          concreteDiagonalPairMapMarkerCells markersSeen ++
            some ConcreteDiagonalPairMapMachineSymbol.marker ::
            concreteDiagonalPairMapRawCells leftRaw
        head := none
        right := [] }
  | m + 1 =>
      { left :=
          concreteDiagonalPairMapMarkerCells markersSeen ++
            some ConcreteDiagonalPairMapMachineSymbol.marker ::
            concreteDiagonalPairMapRawCells leftRaw
        head := some ConcreteDiagonalPairMapMachineSymbol.marker
        right := concreteDiagonalPairMapMarkerCells m }

def concreteDiagonalPairMapReturnMarkerTape
    (leftRaw : Word ConcreteMachineCodeSymbol)
    (markersLeft markersRight : Nat) :
    Tape ConcreteDiagonalPairMapMachineSymbol :=
  { left :=
      concreteDiagonalPairMapMarkerCells markersLeft ++
        concreteDiagonalPairMapRawCells leftRaw
    head := some ConcreteDiagonalPairMapMachineSymbol.marker
    right := concreteDiagonalPairMapMarkerCells markersRight }

def concreteDiagonalPairMapHaltTape (markers : Nat) :
    Tape ConcreteDiagonalPairMapMachineSymbol :=
  match markers with
  | 0 =>
      { left := [none]
        head := none
        right := [] }
  | m + 1 =>
      { left := [none]
        head := some ConcreteDiagonalPairMapMachineSymbol.marker
        right := concreteDiagonalPairMapMarkerCells m }

def concreteDiagonalPairMapConfig
    (state : ConcreteDiagonalPairMapMachineState)
    (tape : Tape ConcreteDiagonalPairMapMachineSymbol) :
    TuringMachine.Configuration
      ConcreteDiagonalPairMapMachineSymbol
      ConcreteDiagonalPairMapMachineState :=
  { state := state, tape := tape }

theorem concreteDiagonalPairMap_initScan_computes
    (seenRev rest : Word ConcreteMachineCodeSymbol) :
    TuringMachine.Computes ConcreteDiagonalPairMapMachine
      (concreteDiagonalPairMapConfig
        ConcreteDiagonalPairMapMachineState.initScan
        (concreteDiagonalPairMapScanTape seenRev rest))
      (concreteDiagonalPairMapConfig
        ConcreteDiagonalPairMapMachineState.return
        (concreteDiagonalPairMapReturnTape
          (List.append rest.reverse seenRev) 1)) := by
  induction rest generalizing seenRev with
  | nil =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (some ConcreteDiagonalPairMapMachineSymbol.marker)
            (concreteDiagonalPairMapScanTape seenRev []))
      refine
        TuringMachine.Computes.step
          (d := concreteDiagonalPairMapConfig
            ConcreteDiagonalPairMapMachineState.return nextTape)
          (TuringMachine.Step.mk
            (write := some ConcreteDiagonalPairMapMachineSymbol.marker)
            (dir := Direction.left)
            (nextState := ConcreteDiagonalPairMapMachineState.return)
            ?_)
          ?_
      · rfl
      · cases seenRev with
        | nil =>
            exact TuringMachine.Computes.refl _
        | cons code suffix =>
            exact TuringMachine.Computes.refl _
  | cons code suffix ih =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (ConcreteDiagonalPairMapMachineSymbol.raw code))
            (concreteDiagonalPairMapScanTape seenRev (code :: suffix)))
      refine
        TuringMachine.Computes.step
          (d := concreteDiagonalPairMapConfig
            ConcreteDiagonalPairMapMachineState.initScan nextTape)
          (TuringMachine.Step.mk
            (write := some (ConcreteDiagonalPairMapMachineSymbol.raw code))
            (dir := Direction.right)
            (nextState := ConcreteDiagonalPairMapMachineState.initScan)
            ?_)
          ?_
      · rfl
      · cases suffix with
        | nil =>
            simpa [nextTape, concreteDiagonalPairMapScanTape,
              concreteDiagonalPairMapRawCells, concreteDiagonalPairMapConfig,
              Tape.move, Tape.moveRight, Tape.write, List.reverse_cons,
              List.append_assoc]
              using ih (code :: seenRev)
        | cons next tail =>
            simpa [nextTape, concreteDiagonalPairMapScanTape,
              concreteDiagonalPairMapRawCells, concreteDiagonalPairMapConfig,
              Tape.move, Tape.moveRight, Tape.write, List.reverse_cons,
              List.append_assoc]
              using ih (code :: seenRev)

theorem concreteDiagonalPairMap_returnMarker_computes
    (leftRaw : Word ConcreteMachineCodeSymbol)
    (markersLeft markersRight : Nat) :
    TuringMachine.Computes ConcreteDiagonalPairMapMachine
      (concreteDiagonalPairMapConfig
        ConcreteDiagonalPairMapMachineState.return
        (concreteDiagonalPairMapReturnMarkerTape
          leftRaw markersLeft markersRight))
      (concreteDiagonalPairMapConfig
        ConcreteDiagonalPairMapMachineState.return
        (concreteDiagonalPairMapReturnTape
          leftRaw (markersLeft + markersRight + 1))) := by
  induction markersLeft generalizing markersRight with
  | zero =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (some ConcreteDiagonalPairMapMachineSymbol.marker)
            (concreteDiagonalPairMapReturnMarkerTape
              leftRaw 0 markersRight))
      refine
        TuringMachine.Computes.step
          (d := concreteDiagonalPairMapConfig
            ConcreteDiagonalPairMapMachineState.return nextTape)
          (TuringMachine.Step.mk
            (write := some ConcreteDiagonalPairMapMachineSymbol.marker)
            (dir := Direction.left)
            (nextState := ConcreteDiagonalPairMapMachineState.return)
            ?_)
          ?_
      · rfl
      · cases leftRaw with
        | nil =>
            simpa [nextTape, concreteDiagonalPairMapReturnMarkerTape,
              concreteDiagonalPairMapReturnTape,
              concreteDiagonalPairMapMarkerCells,
              concreteDiagonalPairMapRawCells,
              concreteDiagonalPairMapConfig, Tape.move, Tape.moveLeft,
              Tape.write]
              using TuringMachine.Computes.refl
                (M := ConcreteDiagonalPairMapMachine)
                (concreteDiagonalPairMapConfig
                  ConcreteDiagonalPairMapMachineState.return nextTape)
        | cons code suffix =>
            simpa [nextTape, concreteDiagonalPairMapReturnMarkerTape,
              concreteDiagonalPairMapReturnTape,
              concreteDiagonalPairMapMarkerCells,
              concreteDiagonalPairMapRawCells,
              concreteDiagonalPairMapConfig, Tape.move, Tape.moveLeft,
              Tape.write]
              using TuringMachine.Computes.refl
                (M := ConcreteDiagonalPairMapMachine)
                (concreteDiagonalPairMapConfig
                  ConcreteDiagonalPairMapMachineState.return nextTape)
  | succ markersLeft ih =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (some ConcreteDiagonalPairMapMachineSymbol.marker)
            (concreteDiagonalPairMapReturnMarkerTape
              leftRaw (markersLeft + 1) markersRight))
      refine
        TuringMachine.Computes.step
          (d := concreteDiagonalPairMapConfig
            ConcreteDiagonalPairMapMachineState.return nextTape)
          (TuringMachine.Step.mk
            (write := some ConcreteDiagonalPairMapMachineSymbol.marker)
            (dir := Direction.left)
            (nextState := ConcreteDiagonalPairMapMachineState.return)
            ?_)
          ?_
      · rfl
      · simpa [nextTape, concreteDiagonalPairMapReturnMarkerTape,
          concreteDiagonalPairMapMarkerCells, concreteDiagonalPairMapConfig,
          Tape.move, Tape.moveLeft, Tape.write, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
          using ih (markersRight + 1)

theorem concreteDiagonalPairMap_markerCells_append_marker_raw
    (n : Nat) (leftRaw : Word ConcreteMachineCodeSymbol) :
    concreteDiagonalPairMapMarkerCells n ++
        some ConcreteDiagonalPairMapMachineSymbol.marker ::
          concreteDiagonalPairMapRawCells leftRaw =
      some ConcreteDiagonalPairMapMachineSymbol.marker ::
        (concreteDiagonalPairMapMarkerCells n ++
          concreteDiagonalPairMapRawCells leftRaw) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        some ConcreteDiagonalPairMapMachineSymbol.marker ::
            (concreteDiagonalPairMapMarkerCells n ++
              some ConcreteDiagonalPairMapMachineSymbol.marker ::
                concreteDiagonalPairMapRawCells leftRaw) =
          some ConcreteDiagonalPairMapMachineSymbol.marker ::
            (some ConcreteDiagonalPairMapMachineSymbol.marker ::
              (concreteDiagonalPairMapMarkerCells n ++
                concreteDiagonalPairMapRawCells leftRaw))
      rw [ih]

theorem concreteDiagonalPairMap_markerCells_succ (n : Nat) :
    concreteDiagonalPairMapMarkerCells (n + 1) =
      some ConcreteDiagonalPairMapMachineSymbol.marker ::
        concreteDiagonalPairMapMarkerCells n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        some ConcreteDiagonalPairMapMachineSymbol.marker ::
            concreteDiagonalPairMapMarkerCells (n + 1) =
          some ConcreteDiagonalPairMapMachineSymbol.marker ::
            some ConcreteDiagonalPairMapMachineSymbol.marker ::
              concreteDiagonalPairMapMarkerCells n
      rw [ih]

theorem concreteDiagonalPairMap_appendBlank_moveLeft
    (leftRaw : Word ConcreteMachineCodeSymbol)
    (markersSeen : Nat) :
    Tape.move Direction.left
      (Tape.write
        (some ConcreteDiagonalPairMapMachineSymbol.marker)
        (concreteDiagonalPairMapAppendScanTape leftRaw markersSeen 0)) =
      concreteDiagonalPairMapReturnMarkerTape leftRaw markersSeen 1 := by
  unfold concreteDiagonalPairMapAppendScanTape
  rw [concreteDiagonalPairMap_markerCells_append_marker_raw]
  simp [concreteDiagonalPairMapReturnMarkerTape,
    concreteDiagonalPairMapMarkerCells,
    Tape.move, Tape.moveLeft, Tape.write]

theorem concreteDiagonalPairMap_appendMarker_moveRight
    (leftRaw : Word ConcreteMachineCodeSymbol)
    (markersSeen markersRemaining : Nat) :
    Tape.move Direction.right
      (Tape.write
        (some ConcreteDiagonalPairMapMachineSymbol.marker)
        (concreteDiagonalPairMapAppendScanTape
          leftRaw markersSeen (markersRemaining + 1))) =
      concreteDiagonalPairMapAppendScanTape
        leftRaw (markersSeen + 1) markersRemaining := by
  cases markersRemaining with
  | zero =>
      unfold concreteDiagonalPairMapAppendScanTape
      rw [concreteDiagonalPairMap_markerCells_succ]
      rfl
  | succ rest =>
      simp [concreteDiagonalPairMapAppendScanTape,
        concreteDiagonalPairMapMarkerCells,
        concreteDiagonalPairMapRawCells,
        Tape.move, Tape.moveRight, Tape.write]
      rw [List.replicate_succ
        (n := rest)
        (a := some ConcreteDiagonalPairMapMachineSymbol.marker)]
      rw [List.replicate_succ
        (n := markersSeen)
        (a := some ConcreteDiagonalPairMapMachineSymbol.marker)]
      simp

theorem concreteDiagonalPairMap_appendScan_computes
    (leftRaw : Word ConcreteMachineCodeSymbol)
    (markersSeen markersRemaining : Nat) :
    TuringMachine.Computes ConcreteDiagonalPairMapMachine
      (concreteDiagonalPairMapConfig
        ConcreteDiagonalPairMapMachineState.append
        (concreteDiagonalPairMapAppendScanTape
          leftRaw markersSeen markersRemaining))
      (concreteDiagonalPairMapConfig
        ConcreteDiagonalPairMapMachineState.return
        (concreteDiagonalPairMapReturnTape
          leftRaw (markersSeen + markersRemaining + 2))) := by
  induction markersRemaining generalizing markersSeen with
  | zero =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (some ConcreteDiagonalPairMapMachineSymbol.marker)
            (concreteDiagonalPairMapAppendScanTape
              leftRaw markersSeen 0))
      refine
        TuringMachine.Computes.step
          (d := concreteDiagonalPairMapConfig
            ConcreteDiagonalPairMapMachineState.return nextTape)
          (TuringMachine.Step.mk
            (write := some ConcreteDiagonalPairMapMachineSymbol.marker)
            (dir := Direction.left)
            (nextState := ConcreteDiagonalPairMapMachineState.return)
            ?_)
          ?_
      · rfl
      · have hnext :
            nextTape =
              concreteDiagonalPairMapReturnMarkerTape
                leftRaw markersSeen 1 := by
          simpa [nextTape]
            using concreteDiagonalPairMap_appendBlank_moveLeft
              leftRaw markersSeen
        rw [hnext]
        simpa [Nat.add_assoc]
          using concreteDiagonalPairMap_returnMarker_computes
            leftRaw markersSeen 1
  | succ markersRemaining ih =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some ConcreteDiagonalPairMapMachineSymbol.marker)
            (concreteDiagonalPairMapAppendScanTape
              leftRaw markersSeen (markersRemaining + 1)))
      refine
        TuringMachine.Computes.step
          (d := concreteDiagonalPairMapConfig
            ConcreteDiagonalPairMapMachineState.append nextTape)
          (TuringMachine.Step.mk
            (write := some ConcreteDiagonalPairMapMachineSymbol.marker)
            (dir := Direction.right)
            (nextState := ConcreteDiagonalPairMapMachineState.append)
            ?_)
          ?_
      · rfl
      · cases markersRemaining with
        | zero =>
            simpa [nextTape, concreteDiagonalPairMapAppendScanTape,
              concreteDiagonalPairMapMarkerCells,
              concreteDiagonalPairMapRawCells,
              concreteDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using ih (markersSeen + 1)
        | succ rest =>
            simpa [nextTape, concreteDiagonalPairMapAppendScanTape,
              concreteDiagonalPairMapMarkerCells,
              concreteDiagonalPairMapRawCells,
              concreteDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
              using ih (markersSeen + 1)

theorem concreteDiagonalPairMap_returnBlank_moveRight (markers : Nat) :
    Tape.move Direction.right
      (Tape.write none
        (concreteDiagonalPairMapReturnTape
          ([] : Word ConcreteMachineCodeSymbol) markers)) =
      concreteDiagonalPairMapHaltTape markers := by
  cases markers with
  | zero =>
      rfl
  | succ markers =>
      rfl

theorem concreteDiagonalPairMap_returnRaw_moveRight
    (code : ConcreteMachineCodeSymbol)
    (rest : Word ConcreteMachineCodeSymbol)
    (markers : Nat) :
    Tape.move Direction.right
      (Tape.write
        (some ConcreteDiagonalPairMapMachineSymbol.marker)
        (concreteDiagonalPairMapReturnTape (code :: rest) markers)) =
      concreteDiagonalPairMapAppendScanTape rest 0 markers := by
  cases markers with
  | zero =>
      rfl
  | succ markers =>
      rfl

theorem concreteDiagonalPairMap_return_computes
    (unprocessedRev : Word ConcreteMachineCodeSymbol) (markers : Nat) :
    TuringMachine.Computes ConcreteDiagonalPairMapMachine
      (concreteDiagonalPairMapConfig
        ConcreteDiagonalPairMapMachineState.return
        (concreteDiagonalPairMapReturnTape unprocessedRev markers))
      (concreteDiagonalPairMapConfig
        ConcreteDiagonalPairMapMachineState.halt
        (concreteDiagonalPairMapHaltTape
          (markers + 2 * unprocessedRev.length))) := by
  induction unprocessedRev generalizing markers with
  | nil =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write none
            (concreteDiagonalPairMapReturnTape
              ([] : Word ConcreteMachineCodeSymbol) markers))
      refine
        TuringMachine.Computes.step
          (d := concreteDiagonalPairMapConfig
            ConcreteDiagonalPairMapMachineState.halt nextTape)
          (TuringMachine.Step.mk
            (write := none)
            (dir := Direction.right)
            (nextState := ConcreteDiagonalPairMapMachineState.halt)
            ?_)
          ?_
      · rfl
      · have hnext :
            nextTape = concreteDiagonalPairMapHaltTape markers := by
          simpa [nextTape]
            using concreteDiagonalPairMap_returnBlank_moveRight markers
        rw [hnext]
        exact TuringMachine.Computes.refl _
  | cons code rest ih =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some ConcreteDiagonalPairMapMachineSymbol.marker)
            (concreteDiagonalPairMapReturnTape
              (code :: rest) markers))
      refine
        TuringMachine.Computes.step
          (d := concreteDiagonalPairMapConfig
            ConcreteDiagonalPairMapMachineState.append nextTape)
          (TuringMachine.Step.mk
            (write := some ConcreteDiagonalPairMapMachineSymbol.marker)
            (dir := Direction.right)
            (nextState := ConcreteDiagonalPairMapMachineState.append)
            ?_)
          ?_
      · rfl
      · have hnext :
            nextTape =
              concreteDiagonalPairMapAppendScanTape rest 0 markers := by
          simpa [nextTape]
            using concreteDiagonalPairMap_returnRaw_moveRight
              code rest markers
        rw [hnext]
        exact
          TuringMachine.computes_trans
            (concreteDiagonalPairMap_appendScan_computes
              rest 0 markers)
            (by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
                Nat.mul_add, Nat.left_distrib, Nat.right_distrib]
                using ih (markers + 2))

theorem concreteDiagonalPairMap_haltTape_normalized (markers : Nat) :
    Tape.normalizedOutput
        (concreteDiagonalPairMapHaltTape markers) =
      List.replicate markers
        ConcreteDiagonalPairMapMachineSymbol.marker := by
  cases markers with
  | zero =>
      rfl
  | succ markers =>
      simp [concreteDiagonalPairMapHaltTape,
        concreteDiagonalPairMapMarkerCells,
        Tape.normalizedOutput, Tape.cells]
      rw [List.replicate_succ]

theorem concreteDiagonalPairMap_outputEncode_const
    (w : Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) :
    EncodeWord concreteDiagonalPairMapOutputEncode w =
      List.replicate w.length
        ConcreteDiagonalPairMapMachineSymbol.marker := by
  induction w with
  | nil =>
      rfl
  | cons symbol rest ih =>
      change
        ConcreteDiagonalPairMapMachineSymbol.marker ::
            EncodeWord concreteDiagonalPairMapOutputEncode rest =
          List.replicate (rest.length + 1)
            ConcreteDiagonalPairMapMachineSymbol.marker
      rw [ih, List.replicate_succ]

theorem concreteDiagonalPairMap_length
    (w : Word ConcreteMachineCodeSymbol) :
    (ConcreteDiagonalPairMap w).length =
      w.length + 1 + w.length := by
  unfold ConcreteDiagonalPairMap PairCodeSymbol.diagonalMap
    PairCodeSymbol.encodePair
  change
    (List.append
      (List.append (List.map PairCodeSymbol.left w)
        [PairCodeSymbol.separator])
      (List.map PairCodeSymbol.right w)).length =
        w.length + 1 + w.length
  simp [List.length_append]
  omega

theorem concreteDiagonalPairMap_outputEncode_eq_replicate
    (w : Word ConcreteMachineCodeSymbol) :
    EncodeWord concreteDiagonalPairMapOutputEncode
        (ConcreteDiagonalPairMap w) =
      List.replicate (w.length + 1 + w.length)
        ConcreteDiagonalPairMapMachineSymbol.marker := by
  rw [concreteDiagonalPairMap_outputEncode_const,
    concreteDiagonalPairMap_length]

theorem concreteDiagonalPairMap_startRaw_moveRight
    (code : ConcreteMachineCodeSymbol)
    (rest : Word ConcreteMachineCodeSymbol) :
    Tape.move Direction.right
      (Tape.write
        (some (ConcreteDiagonalPairMapMachineSymbol.raw code))
        (Tape.input
          (EncodeWord concreteDiagonalPairMapInputEncode
            (code :: rest)))) =
      concreteDiagonalPairMapScanTape [code] rest := by
  cases rest with
  | nil =>
      rfl
  | cons next suffix =>
      simp [EncodeWord, concreteDiagonalPairMapInputEncode,
        concreteDiagonalPairMapScanTape,
        concreteDiagonalPairMapRawCells, Tape.input,
        Tape.move, Tape.moveRight, Tape.write]

theorem concrete_diagonal_pair_map_computable_noninjective :
    ConcreteDiagonalPairMapComputable := by
  unfold ConcreteDiagonalPairMapComputable TuringComputable ComputesFunction
  refine
    ⟨ ConcreteDiagonalPairMapMachineSymbol
    , ConcreteDiagonalPairMapMachineState
    , ConcreteDiagonalPairMapMachine
    , concreteDiagonalPairMapInputEncode
    , concreteDiagonalPairMapOutputEncode
    , ?_ ⟩
  intro w
  cases w with
  | nil =>
      let finalTape :=
        Tape.move Direction.right
          (Tape.write
            (some ConcreteDiagonalPairMapMachineSymbol.marker)
            (Tape.input
              (EncodeWord concreteDiagonalPairMapInputEncode
                ([] : Word ConcreteMachineCodeSymbol))))
      refine
        ⟨ concreteDiagonalPairMapConfig
            ConcreteDiagonalPairMapMachineState.halt finalTape
        , ?_, rfl, ?_ ⟩
      · refine
          TuringMachine.Computes.step
            (d := concreteDiagonalPairMapConfig
              ConcreteDiagonalPairMapMachineState.halt finalTape)
            (TuringMachine.Step.mk
              (write := some ConcreteDiagonalPairMapMachineSymbol.marker)
              (dir := Direction.right)
              (nextState := ConcreteDiagonalPairMapMachineState.halt)
              ?_)
            (TuringMachine.Computes.refl _)
        rfl
      · rw [concreteDiagonalPairMap_outputEncode_eq_replicate]
        change Tape.normalizedOutput finalTape =
          [ConcreteDiagonalPairMapMachineSymbol.marker]
        simp [finalTape, EncodeWord, Tape.input, Tape.blank, Tape.write,
          Tape.move, Tape.moveRight, Tape.normalizedOutput, Tape.cells]
  | cons code rest =>
      let startNextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (ConcreteDiagonalPairMapMachineSymbol.raw code))
            (Tape.input
              (EncodeWord concreteDiagonalPairMapInputEncode
                (code :: rest))))
      let returnRev : Word ConcreteMachineCodeSymbol :=
        List.append rest.reverse [code]
      let finalMarkers := 1 + 2 * returnRev.length
      refine
        ⟨ concreteDiagonalPairMapConfig
            ConcreteDiagonalPairMapMachineState.halt
            (concreteDiagonalPairMapHaltTape finalMarkers)
        , ?_, rfl, ?_ ⟩
      · refine
          TuringMachine.Computes.step
            (d := concreteDiagonalPairMapConfig
              ConcreteDiagonalPairMapMachineState.initScan startNextTape)
            (TuringMachine.Step.mk
              (write := some
                (ConcreteDiagonalPairMapMachineSymbol.raw code))
              (dir := Direction.right)
              (nextState := ConcreteDiagonalPairMapMachineState.initScan)
              ?_)
            ?_
        · rfl
        · have hstart :
              startNextTape =
                concreteDiagonalPairMapScanTape [code] rest := by
            simpa [startNextTape]
              using concreteDiagonalPairMap_startRaw_moveRight code rest
          rw [hstart]
          exact
            TuringMachine.computes_trans
              (concreteDiagonalPairMap_initScan_computes [code] rest)
              (concreteDiagonalPairMap_return_computes returnRev 1)
      · change
          Tape.normalizedOutput
              (concreteDiagonalPairMapHaltTape finalMarkers) =
            EncodeWord concreteDiagonalPairMapOutputEncode
              (ConcreteDiagonalPairMap (code :: rest))
        rw [concreteDiagonalPairMap_haltTape_normalized,
          concreteDiagonalPairMap_outputEncode_eq_replicate]
        congr 1
        simp [finalMarkers, returnRev, List.length_append,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        omega

theorem concrete_diagonal_pair_map_computable :
    ConcreteDiagonalPairMapComputable :=
  concrete_diagonal_pair_map_computable_noninjective

/-!
# Faithful copy machine

The faithful machine below preserves the concrete pair-code alphabet through an
injective output encoding. It scans the input once to append the separator,
rewinds to the left edge, and then processes input symbols from left to right.
For each raw code symbol it temporarily marks the left-copy cell, appends the
matching right-copy tag at the far right, returns to the temporary mark, turns
it into the final left tag, and advances to the next unprocessed raw cell.
-/

inductive FaithfulDiagonalPairMapMachineSymbol where
  | raw : ConcreteMachineCodeSymbol -> FaithfulDiagonalPairMapMachineSymbol
  | markLeft : ConcreteMachineCodeSymbol -> FaithfulDiagonalPairMapMachineSymbol
  | out : ConcretePairCodeSymbol ConcreteMachineCodeSymbol ->
      FaithfulDiagonalPairMapMachineSymbol

namespace FaithfulDiagonalPairMapMachineSymbol

def finite : Foundation.FiniteType FaithfulDiagonalPairMapMachineSymbol where
  elems :=
    ConcreteMachineCodeSymbolFinite.elems.map
      FaithfulDiagonalPairMapMachineSymbol.raw ++
    ConcreteMachineCodeSymbolFinite.elems.map
      FaithfulDiagonalPairMapMachineSymbol.markLeft ++
    (PairCodeSymbol.finite ConcreteMachineCodeSymbolFinite).elems.map
      FaithfulDiagonalPairMapMachineSymbol.out
  complete := by
    intro symbol
    cases symbol with
    | raw code =>
        simp [ConcreteMachineCodeSymbolFinite.complete code]
    | markLeft code =>
        simp [ConcreteMachineCodeSymbolFinite.complete code]
    | out pair =>
        simp
        exact (PairCodeSymbol.finite ConcreteMachineCodeSymbolFinite).complete
          pair

end FaithfulDiagonalPairMapMachineSymbol

inductive FaithfulDiagonalPairMapMachineState where
  | initStart
  | initScan
  | rewind
  | process
  | append : ConcreteMachineCodeSymbol -> FaithfulDiagonalPairMapMachineState
  | seekMark
  | halt

namespace FaithfulDiagonalPairMapMachineState

def finite : Foundation.FiniteType FaithfulDiagonalPairMapMachineState where
  elems :=
    [ FaithfulDiagonalPairMapMachineState.initStart
    , FaithfulDiagonalPairMapMachineState.initScan
    , FaithfulDiagonalPairMapMachineState.rewind
    , FaithfulDiagonalPairMapMachineState.process
    , FaithfulDiagonalPairMapMachineState.seekMark
    , FaithfulDiagonalPairMapMachineState.halt
    ] ++ ConcreteMachineCodeSymbolFinite.elems.map
      FaithfulDiagonalPairMapMachineState.append
  complete := by
    intro state
    cases state with
    | initStart => simp
    | initScan => simp
    | rewind => simp
    | process => simp
    | append code =>
        simp [ConcreteMachineCodeSymbolFinite.complete code]
    | seekMark => simp
    | halt => simp

end FaithfulDiagonalPairMapMachineState

inductive FaithfulDiagonalPairMapScanCell where
  | raw : ConcreteMachineCodeSymbol -> FaithfulDiagonalPairMapScanCell
  | separator : FaithfulDiagonalPairMapScanCell
  | right : ConcreteMachineCodeSymbol -> FaithfulDiagonalPairMapScanCell

def faithfulDiagonalPairMapInputEncode
    (code : ConcreteMachineCodeSymbol) :
    FaithfulDiagonalPairMapMachineSymbol :=
  FaithfulDiagonalPairMapMachineSymbol.raw code

def faithfulDiagonalPairMapOutputEncode
    (pair : ConcretePairCodeSymbol ConcreteMachineCodeSymbol) :
    FaithfulDiagonalPairMapMachineSymbol :=
  FaithfulDiagonalPairMapMachineSymbol.out pair

theorem faithfulDiagonalPairMapInputEncode_injective :
    Function.Injective faithfulDiagonalPairMapInputEncode := by
  intro a b h
  cases h
  rfl

theorem faithfulDiagonalPairMapOutputEncode_injective :
    Function.Injective faithfulDiagonalPairMapOutputEncode := by
  intro a b h
  cases h
  rfl

def faithfulDiagonalPairMapScanCellEncode :
    FaithfulDiagonalPairMapScanCell ->
      Option FaithfulDiagonalPairMapMachineSymbol
  | FaithfulDiagonalPairMapScanCell.raw code =>
      some (FaithfulDiagonalPairMapMachineSymbol.raw code)
  | FaithfulDiagonalPairMapScanCell.separator =>
      some (FaithfulDiagonalPairMapMachineSymbol.out
        PairCodeSymbol.separator)
  | FaithfulDiagonalPairMapScanCell.right code =>
      some (FaithfulDiagonalPairMapMachineSymbol.out
        (PairCodeSymbol.right code))

def faithfulDiagonalPairMapScanCells
    (remaining processed : Word ConcreteMachineCodeSymbol) :
    List FaithfulDiagonalPairMapScanCell :=
  remaining.map FaithfulDiagonalPairMapScanCell.raw ++
    [FaithfulDiagonalPairMapScanCell.separator] ++
      processed.map FaithfulDiagonalPairMapScanCell.right

def faithfulDiagonalPairMapScanTapeCells
    (cells : List FaithfulDiagonalPairMapScanCell) :
    List (Option FaithfulDiagonalPairMapMachineSymbol) :=
  cells.map faithfulDiagonalPairMapScanCellEncode

def faithfulDiagonalPairMapLeftCells
    (processed : Word ConcreteMachineCodeSymbol) :
    List (Option FaithfulDiagonalPairMapMachineSymbol) :=
  processed.map (fun code =>
    some (FaithfulDiagonalPairMapMachineSymbol.out
      (PairCodeSymbol.left code)))

def faithfulDiagonalPairMapRightCells
    (processed : Word ConcreteMachineCodeSymbol) :
    List (Option FaithfulDiagonalPairMapMachineSymbol) :=
  processed.map (fun code =>
    some (FaithfulDiagonalPairMapMachineSymbol.out
      (PairCodeSymbol.right code)))

def faithfulDiagonalPairMapLeftContext
    (processed : Word ConcreteMachineCodeSymbol) :
    List (Option FaithfulDiagonalPairMapMachineSymbol) :=
  (faithfulDiagonalPairMapLeftCells processed).reverse ++ [none]

def faithfulDiagonalPairMapMarkedLeftContext
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol) :
    List (Option FaithfulDiagonalPairMapMachineSymbol) :=
  some (FaithfulDiagonalPairMapMachineSymbol.markLeft code) ::
    faithfulDiagonalPairMapLeftContext processed

def faithfulDiagonalPairMapProcessScanTape
    (processed : Word ConcreteMachineCodeSymbol)
    (cells : List FaithfulDiagonalPairMapScanCell) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  match faithfulDiagonalPairMapScanTapeCells cells with
  | [] =>
      { left := faithfulDiagonalPairMapLeftContext processed
        head := none
        right := [] }
  | cell :: rest =>
      { left := faithfulDiagonalPairMapLeftContext processed
        head := cell
        right := rest }

def faithfulDiagonalPairMapProcessTape
    (processed remaining : Word ConcreteMachineCodeSymbol) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  faithfulDiagonalPairMapProcessScanTape processed
    (faithfulDiagonalPairMapScanCells remaining processed)

def faithfulDiagonalPairMapInitScanTape
    (seenRev rest : Word ConcreteMachineCodeSymbol) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  match rest with
  | [] =>
      { left :=
          seenRev.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code))
        head := none
        right := [] }
  | code :: suffix =>
      { left :=
          seenRev.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code))
        head := some (FaithfulDiagonalPairMapMachineSymbol.raw code)
        right :=
          suffix.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code)) }

def faithfulDiagonalPairMapRewindTape
    (leftRev crossed : Word ConcreteMachineCodeSymbol) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  match leftRev with
  | [] =>
      { left := []
        head := none
        right :=
          crossed.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code)) ++
            [some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator)] }
  | code :: rest =>
      { left :=
          rest.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code))
        head := some (FaithfulDiagonalPairMapMachineSymbol.raw code)
        right :=
          crossed.map (fun code =>
            some (FaithfulDiagonalPairMapMachineSymbol.raw code)) ++
            [some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator)] }

def faithfulDiagonalPairMapAppendScanTape
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol)
    (scannedRev remaining : List FaithfulDiagonalPairMapScanCell) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  match remaining with
  | [] =>
      { left :=
          faithfulDiagonalPairMapScanTapeCells scannedRev ++
            faithfulDiagonalPairMapMarkedLeftContext processed code
        head := none
        right := [] }
  | cell :: rest =>
      { left :=
          faithfulDiagonalPairMapScanTapeCells scannedRev ++
            faithfulDiagonalPairMapMarkedLeftContext processed code
        head := faithfulDiagonalPairMapScanCellEncode cell
        right := faithfulDiagonalPairMapScanTapeCells rest }

def faithfulDiagonalPairMapSeekTape
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol)
    (leftRev crossed : List FaithfulDiagonalPairMapScanCell) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  match leftRev with
  | [] =>
      { left := faithfulDiagonalPairMapLeftContext processed
        head := some (FaithfulDiagonalPairMapMachineSymbol.markLeft code)
        right :=
          faithfulDiagonalPairMapScanTapeCells crossed ++
            [some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.right code))] }
  | cell :: rest =>
      { left :=
          faithfulDiagonalPairMapScanTapeCells rest ++
            faithfulDiagonalPairMapMarkedLeftContext processed code
        head := faithfulDiagonalPairMapScanCellEncode cell
        right :=
          faithfulDiagonalPairMapScanTapeCells crossed ++
            [some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.right code))] }

def faithfulDiagonalPairMapHaltTape
    (processed : Word ConcreteMachineCodeSymbol) :
    Tape FaithfulDiagonalPairMapMachineSymbol :=
  Tape.move Direction.right
    (Tape.write
      (some (FaithfulDiagonalPairMapMachineSymbol.out
        PairCodeSymbol.separator))
      (faithfulDiagonalPairMapProcessTape processed []))

def faithfulDiagonalPairMapConfig
    (state : FaithfulDiagonalPairMapMachineState)
    (tape : Tape FaithfulDiagonalPairMapMachineSymbol) :
    TuringMachine.Configuration
      FaithfulDiagonalPairMapMachineSymbol
      FaithfulDiagonalPairMapMachineState :=
  { state := state, tape := tape }

def faithfulDiagonalPairMapTransition :
    FaithfulDiagonalPairMapMachineState ->
      Option FaithfulDiagonalPairMapMachineSymbol ->
        Option
          (Option FaithfulDiagonalPairMapMachineSymbol × Direction ×
            FaithfulDiagonalPairMapMachineState)
  | FaithfulDiagonalPairMapMachineState.initStart, none =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.out
          PairCodeSymbol.separator),
          Direction.right,
          FaithfulDiagonalPairMapMachineState.halt)
  | FaithfulDiagonalPairMapMachineState.initStart,
      some (FaithfulDiagonalPairMapMachineSymbol.raw code) =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.raw code),
          Direction.right,
          FaithfulDiagonalPairMapMachineState.initScan)
  | FaithfulDiagonalPairMapMachineState.initStart,
      some cell =>
      some (some cell, Direction.right,
        FaithfulDiagonalPairMapMachineState.initScan)
  | FaithfulDiagonalPairMapMachineState.initScan, none =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.out
          PairCodeSymbol.separator),
          Direction.left,
          FaithfulDiagonalPairMapMachineState.rewind)
  | FaithfulDiagonalPairMapMachineState.initScan,
      some cell =>
      some (some cell, Direction.right,
        FaithfulDiagonalPairMapMachineState.initScan)
  | FaithfulDiagonalPairMapMachineState.rewind, none =>
      some (none, Direction.right,
        FaithfulDiagonalPairMapMachineState.process)
  | FaithfulDiagonalPairMapMachineState.rewind,
      some cell =>
      some (some cell, Direction.left,
        FaithfulDiagonalPairMapMachineState.rewind)
  | FaithfulDiagonalPairMapMachineState.process,
      some (FaithfulDiagonalPairMapMachineSymbol.raw code) =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.markLeft code),
          Direction.right,
          FaithfulDiagonalPairMapMachineState.append code)
  | FaithfulDiagonalPairMapMachineState.process,
      some (FaithfulDiagonalPairMapMachineSymbol.out
        PairCodeSymbol.separator) =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.out
          PairCodeSymbol.separator),
          Direction.right,
          FaithfulDiagonalPairMapMachineState.halt)
  | FaithfulDiagonalPairMapMachineState.process, cell =>
      some (cell, Direction.right,
        FaithfulDiagonalPairMapMachineState.process)
  | FaithfulDiagonalPairMapMachineState.append code, none =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.out
          (PairCodeSymbol.right code)),
          Direction.left,
          FaithfulDiagonalPairMapMachineState.seekMark)
  | FaithfulDiagonalPairMapMachineState.append code,
      some cell =>
      some (some cell, Direction.right,
        FaithfulDiagonalPairMapMachineState.append code)
  | FaithfulDiagonalPairMapMachineState.seekMark,
      some (FaithfulDiagonalPairMapMachineSymbol.markLeft code) =>
      some
        (some (FaithfulDiagonalPairMapMachineSymbol.out
          (PairCodeSymbol.left code)),
          Direction.right,
          FaithfulDiagonalPairMapMachineState.process)
  | FaithfulDiagonalPairMapMachineState.seekMark,
      some cell =>
      some (some cell, Direction.left,
        FaithfulDiagonalPairMapMachineState.seekMark)
  | FaithfulDiagonalPairMapMachineState.seekMark, none =>
      some (none, Direction.right,
        FaithfulDiagonalPairMapMachineState.process)
  | FaithfulDiagonalPairMapMachineState.halt, _ =>
      none

def FaithfulConcreteDiagonalPairMapMachine :
    TuringMachine
      FaithfulDiagonalPairMapMachineSymbol
      FaithfulDiagonalPairMapMachineState where
  start := FaithfulDiagonalPairMapMachineState.initStart
  halt := FaithfulDiagonalPairMapMachineState.halt
  transition := faithfulDiagonalPairMapTransition
  statesFinite := FaithfulDiagonalPairMapMachineState.finite

theorem faithfulDiagonalPairMapScanTapeCells_append
    (x y : List FaithfulDiagonalPairMapScanCell) :
    faithfulDiagonalPairMapScanTapeCells (x ++ y) =
      faithfulDiagonalPairMapScanTapeCells x ++
        faithfulDiagonalPairMapScanTapeCells y := by
  simp [faithfulDiagonalPairMapScanTapeCells]

theorem faithfulDiagonalPairMapLeftContext_append_single
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol) :
    faithfulDiagonalPairMapLeftContext (List.append processed [code]) =
      some (FaithfulDiagonalPairMapMachineSymbol.out
        (PairCodeSymbol.left code)) ::
        faithfulDiagonalPairMapLeftContext processed := by
  simp [faithfulDiagonalPairMapLeftContext,
    faithfulDiagonalPairMapLeftCells, List.map_append]

theorem faithfulDiagonalPairMapScanCells_append_processed
    (remaining processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol) :
    faithfulDiagonalPairMapScanCells remaining (List.append processed [code]) =
      faithfulDiagonalPairMapScanCells remaining processed ++
        [FaithfulDiagonalPairMapScanCell.right code] := by
  simp [faithfulDiagonalPairMapScanCells, List.map_append,
    List.append_assoc]

theorem faithfulDiagonalPairMap_filterMap_some_map
    {alpha beta : Type} (f : alpha -> beta) (w : List alpha) :
    List.filterMap (fun a => some (f a)) w = w.map f := by
  induction w with
  | nil =>
      rfl
  | cons a rest ih =>
      simp [ih]

theorem faithfulDiagonalPairMap_output_left_map
    (w : Word ConcreteMachineCodeSymbol) :
    List.map
        (fun code =>
          FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.left code)) w =
      List.map
        (fun pair => FaithfulDiagonalPairMapMachineSymbol.out pair)
        (List.map PairCodeSymbol.left w) := by
  induction w with
  | nil =>
      rfl
  | cons code rest ih =>
      change
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.left code) ::
          List.map
            (fun code =>
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.left code)) rest =
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.left code) ::
          List.map
            (fun pair => FaithfulDiagonalPairMapMachineSymbol.out pair)
            (List.map PairCodeSymbol.left rest)
      rw [ih]

theorem faithfulDiagonalPairMap_output_right_map
    (w : Word ConcreteMachineCodeSymbol) :
    List.map
        (fun code =>
          FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.right code)) w =
      List.map
        (fun pair => FaithfulDiagonalPairMapMachineSymbol.out pair)
        (List.map PairCodeSymbol.right w) := by
  induction w with
  | nil =>
      rfl
  | cons code rest ih =>
      change
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.right code) ::
          List.map
            (fun code =>
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.right code)) rest =
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.right code) ::
          List.map
            (fun pair => FaithfulDiagonalPairMapMachineSymbol.out pair)
            (List.map PairCodeSymbol.right rest)
      rw [ih]

theorem faithfulDiagonalPairMap_initScan_computes
    (seenRev rest : Word ConcreteMachineCodeSymbol) :
    TuringMachine.Computes FaithfulConcreteDiagonalPairMapMachine
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.initScan
        (faithfulDiagonalPairMapInitScanTape seenRev rest))
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.rewind
        (faithfulDiagonalPairMapRewindTape
          (List.append rest.reverse seenRev) [])) := by
  induction rest generalizing seenRev with
  | nil =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator))
            (faithfulDiagonalPairMapInitScanTape seenRev []))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.rewind nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator))
            (dir := Direction.left)
            (nextState := FaithfulDiagonalPairMapMachineState.rewind)
            ?_)
          ?_
      · rfl
      · cases seenRev with
        | nil =>
            exact TuringMachine.Computes.refl _
        | cons code suffix =>
            exact TuringMachine.Computes.refl _
  | cons code suffix ih =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.raw code))
            (faithfulDiagonalPairMapInitScanTape seenRev (code :: suffix)))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.initScan nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.raw code))
            (dir := Direction.right)
            (nextState := FaithfulDiagonalPairMapMachineState.initScan)
            ?_)
          ?_
      · rfl
      · cases suffix with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapInitScanTape,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (code :: seenRev)
        | cons next tail =>
            simpa [nextTape, faithfulDiagonalPairMapInitScanTape,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (code :: seenRev)

theorem faithfulDiagonalPairMap_rewind_computes
    (leftRev crossed : Word ConcreteMachineCodeSymbol) :
    TuringMachine.Computes FaithfulConcreteDiagonalPairMapMachine
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.rewind
        (faithfulDiagonalPairMapRewindTape leftRev crossed))
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.process
        (faithfulDiagonalPairMapProcessTape []
          (List.append leftRev.reverse crossed))) := by
  induction leftRev generalizing crossed with
  | nil =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write none
            (faithfulDiagonalPairMapRewindTape
              ([] : Word ConcreteMachineCodeSymbol) crossed))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.process nextTape)
          (TuringMachine.Step.mk
            (write := none)
            (dir := Direction.right)
            (nextState := FaithfulDiagonalPairMapMachineState.process)
            ?_)
          ?_
      · rfl
      · cases crossed with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapRewindTape,
              faithfulDiagonalPairMapProcessTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanCells,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write]
              using TuringMachine.Computes.refl
                (M := FaithfulConcreteDiagonalPairMapMachine)
                (faithfulDiagonalPairMapConfig
                  FaithfulDiagonalPairMapMachineState.process nextTape)
        | cons code rest =>
            simpa [nextTape, faithfulDiagonalPairMapRewindTape,
              faithfulDiagonalPairMapProcessTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanCells,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write]
              using TuringMachine.Computes.refl
                (M := FaithfulConcreteDiagonalPairMapMachine)
                (faithfulDiagonalPairMapConfig
                  FaithfulDiagonalPairMapMachineState.process nextTape)
  | cons code rest ih =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.raw code))
            (faithfulDiagonalPairMapRewindTape (code :: rest) crossed))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.rewind nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.raw code))
            (dir := Direction.left)
            (nextState := FaithfulDiagonalPairMapMachineState.rewind)
            ?_)
          ?_
      · rfl
      · cases rest with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapRewindTape,
              faithfulDiagonalPairMapProcessTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanCells,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveLeft,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (code :: crossed)
        | cons next tail =>
            simpa [nextTape, faithfulDiagonalPairMapRewindTape,
              faithfulDiagonalPairMapProcessTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanCells,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveLeft,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (code :: crossed)

theorem faithfulDiagonalPairMap_appendScan_computes
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol)
    (scannedRev remaining : List FaithfulDiagonalPairMapScanCell) :
    TuringMachine.Computes FaithfulConcreteDiagonalPairMapMachine
      (faithfulDiagonalPairMapConfig
        (FaithfulDiagonalPairMapMachineState.append code)
        (faithfulDiagonalPairMapAppendScanTape
          processed code scannedRev remaining))
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.seekMark
        (faithfulDiagonalPairMapSeekTape
          processed code (remaining.reverse ++ scannedRev) [])) := by
  induction remaining generalizing scannedRev with
  | nil =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.right code)))
            (faithfulDiagonalPairMapAppendScanTape
              processed code scannedRev []))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.seekMark nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.right code)))
            (dir := Direction.left)
            (nextState := FaithfulDiagonalPairMapMachineState.seekMark)
            ?_)
          ?_
      · rfl
      · cases scannedRev with
        | nil =>
            exact TuringMachine.Computes.refl _
        | cons cell rest =>
            exact TuringMachine.Computes.refl _
  | cons cell rest ih =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (faithfulDiagonalPairMapScanCellEncode cell)
            (faithfulDiagonalPairMapAppendScanTape
              processed code scannedRev (cell :: rest)))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            (FaithfulDiagonalPairMapMachineState.append code) nextTape)
          (TuringMachine.Step.mk
            (write := faithfulDiagonalPairMapScanCellEncode cell)
            (dir := Direction.right)
            (nextState := FaithfulDiagonalPairMapMachineState.append code)
            ?_)
          ?_
      · cases cell <;> rfl
      · cases rest with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapAppendScanTape,
              faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (cell :: scannedRev)
        | cons next tail =>
            simpa [nextTape, faithfulDiagonalPairMapAppendScanTape,
              faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (cell :: scannedRev)

theorem faithfulDiagonalPairMap_seek_computes
    (processed : Word ConcreteMachineCodeSymbol)
    (code : ConcreteMachineCodeSymbol)
    (leftRev crossed : List FaithfulDiagonalPairMapScanCell) :
    TuringMachine.Computes FaithfulConcreteDiagonalPairMapMachine
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.seekMark
        (faithfulDiagonalPairMapSeekTape
          processed code leftRev crossed))
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.process
        (faithfulDiagonalPairMapProcessScanTape
          (List.append processed [code])
          (leftRev.reverse ++ crossed ++
            [FaithfulDiagonalPairMapScanCell.right code]))) := by
  induction leftRev generalizing crossed with
  | nil =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.left code)))
            (faithfulDiagonalPairMapSeekTape processed code [] crossed))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.process nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.out
              (PairCodeSymbol.left code)))
            (dir := Direction.right)
            (nextState := FaithfulDiagonalPairMapMachineState.process)
            ?_)
          ?_
      · rfl
      · cases crossed with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells, List.map_append,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write]
              using TuringMachine.Computes.refl
                (M := FaithfulConcreteDiagonalPairMapMachine)
                (faithfulDiagonalPairMapConfig
                  FaithfulDiagonalPairMapMachineState.process nextTape)
        | cons cell rest =>
            simpa [nextTape, faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapLeftContext,
              faithfulDiagonalPairMapLeftCells, List.map_append,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveRight,
              Tape.write]
              using TuringMachine.Computes.refl
                (M := FaithfulConcreteDiagonalPairMapMachine)
                (faithfulDiagonalPairMapConfig
                  FaithfulDiagonalPairMapMachineState.process nextTape)
  | cons cell rest ih =>
      let nextTape :=
        Tape.move Direction.left
          (Tape.write
            (faithfulDiagonalPairMapScanCellEncode cell)
            (faithfulDiagonalPairMapSeekTape
              processed code (cell :: rest) crossed))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.seekMark nextTape)
          (TuringMachine.Step.mk
            (write := faithfulDiagonalPairMapScanCellEncode cell)
            (dir := Direction.left)
            (nextState := FaithfulDiagonalPairMapMachineState.seekMark)
            ?_)
          ?_
      · cases cell <;> rfl
      · cases rest with
        | nil =>
            simpa [nextTape, faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveLeft,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (cell :: crossed)
        | cons next tail =>
            simpa [nextTape, faithfulDiagonalPairMapSeekTape,
              faithfulDiagonalPairMapProcessScanTape,
              faithfulDiagonalPairMapScanTapeCells,
              faithfulDiagonalPairMapScanCellEncode,
              faithfulDiagonalPairMapConfig, Tape.move, Tape.moveLeft,
              Tape.write, List.reverse_cons, List.append_assoc]
              using ih (cell :: crossed)

theorem faithfulDiagonalPairMap_process_computes
    (processed remaining : Word ConcreteMachineCodeSymbol) :
    TuringMachine.Computes FaithfulConcreteDiagonalPairMapMachine
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.process
        (faithfulDiagonalPairMapProcessTape processed remaining))
      (faithfulDiagonalPairMapConfig
        FaithfulDiagonalPairMapMachineState.halt
        (faithfulDiagonalPairMapHaltTape
          (List.append processed remaining))) := by
  induction remaining generalizing processed with
  | nil =>
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator))
            (faithfulDiagonalPairMapProcessTape processed []))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.halt nextTape)
          (TuringMachine.Step.mk
            (write := some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator))
            (dir := Direction.right)
            (nextState := FaithfulDiagonalPairMapMachineState.halt)
            ?_)
          ?_
      · rfl
      · simpa [nextTape, faithfulDiagonalPairMapHaltTape]
          using TuringMachine.Computes.refl
            (M := FaithfulConcreteDiagonalPairMapMachine)
            (faithfulDiagonalPairMapConfig
              FaithfulDiagonalPairMapMachineState.halt nextTape)
  | cons code rest ih =>
      let scanRest := faithfulDiagonalPairMapScanCells rest processed
      let nextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.markLeft code))
            (faithfulDiagonalPairMapProcessTape processed
              (code :: rest)))
      refine
        TuringMachine.Computes.step
          (d := faithfulDiagonalPairMapConfig
            (FaithfulDiagonalPairMapMachineState.append code) nextTape)
          (TuringMachine.Step.mk
            (write := some
              (FaithfulDiagonalPairMapMachineSymbol.markLeft code))
            (dir := Direction.right)
            (nextState :=
              FaithfulDiagonalPairMapMachineState.append code)
            ?_)
          ?_
      · rfl
      · have hnext :
            nextTape =
              faithfulDiagonalPairMapAppendScanTape
                processed code [] scanRest := by
          cases rest with
          | nil =>
              simp [nextTape, scanRest, faithfulDiagonalPairMapProcessTape,
                faithfulDiagonalPairMapProcessScanTape,
                faithfulDiagonalPairMapAppendScanTape,
                faithfulDiagonalPairMapScanCells,
                faithfulDiagonalPairMapScanTapeCells,
                faithfulDiagonalPairMapScanCellEncode,
                faithfulDiagonalPairMapMarkedLeftContext,
                Tape.move, Tape.moveRight, Tape.write]
          | cons next suffix =>
              simp [nextTape, scanRest, faithfulDiagonalPairMapProcessTape,
                faithfulDiagonalPairMapProcessScanTape,
                faithfulDiagonalPairMapAppendScanTape,
                faithfulDiagonalPairMapScanCells,
                faithfulDiagonalPairMapScanTapeCells,
                faithfulDiagonalPairMapScanCellEncode,
                faithfulDiagonalPairMapMarkedLeftContext,
                Tape.move, Tape.moveRight, Tape.write]
        rw [hnext]
        refine
          TuringMachine.computes_trans
            (faithfulDiagonalPairMap_appendScan_computes
              processed code [] scanRest)
            ?_
        refine
          TuringMachine.computes_trans
            (by
              simpa [scanRest, List.reverse_append,
                faithfulDiagonalPairMapScanCells,
                List.append_assoc]
                using
                  faithfulDiagonalPairMap_seek_computes
                    processed code scanRest.reverse [])
            ?_
        simpa [faithfulDiagonalPairMapProcessTape,
          faithfulDiagonalPairMapScanCells, List.map_append,
          List.append_assoc]
          using ih (List.append processed [code])

theorem faithfulDiagonalPairMap_haltTape_normalized
    (w : Word ConcreteMachineCodeSymbol) :
    Tape.normalizedOutput (faithfulDiagonalPairMapHaltTape w) =
      EncodeWord faithfulDiagonalPairMapOutputEncode
        (ConcreteDiagonalPairMap w) := by
  cases w with
  | nil =>
      simp [faithfulDiagonalPairMapHaltTape,
        faithfulDiagonalPairMapProcessTape,
        faithfulDiagonalPairMapProcessScanTape,
        faithfulDiagonalPairMapScanCells,
        faithfulDiagonalPairMapScanTapeCells,
        faithfulDiagonalPairMapScanCellEncode,
        faithfulDiagonalPairMapLeftContext,
        faithfulDiagonalPairMapLeftCells,
        ConcreteDiagonalPairMap,
        PairCodeSymbol.diagonalMap,
        PairCodeSymbol.encodePair,
        EncodeWord,
        Tape.move, Tape.moveRight, Tape.write, Tape.normalizedOutput,
        Tape.cells]
      change
        [FaithfulDiagonalPairMapMachineSymbol.out
          PairCodeSymbol.separator] =
        [FaithfulDiagonalPairMapMachineSymbol.out
          PairCodeSymbol.separator]
      rfl
  | cons code rest =>
      simp [faithfulDiagonalPairMapHaltTape,
        faithfulDiagonalPairMapProcessTape,
        faithfulDiagonalPairMapProcessScanTape,
        faithfulDiagonalPairMapScanCells,
        faithfulDiagonalPairMapScanTapeCells,
        faithfulDiagonalPairMapScanCellEncode,
        faithfulDiagonalPairMapLeftContext,
        faithfulDiagonalPairMapLeftCells,
        ConcreteDiagonalPairMap,
        PairCodeSymbol.diagonalMap,
        PairCodeSymbol.encodePair,
        EncodeWord,
        Tape.move, Tape.moveRight, Tape.write, Tape.normalizedOutput,
        Tape.cells, Function.comp_def,
        faithfulDiagonalPairMap_filterMap_some_map]
      unfold faithfulDiagonalPairMapOutputEncode
      change
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.left code) ::
          (List.map
              (fun code =>
                FaithfulDiagonalPairMapMachineSymbol.out
                  (PairCodeSymbol.left code)) rest ++
            FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator ::
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.right code) ::
                List.map
                  (fun code =>
                    FaithfulDiagonalPairMapMachineSymbol.out
                      (PairCodeSymbol.right code)) rest) =
        FaithfulDiagonalPairMapMachineSymbol.out
            (PairCodeSymbol.left code) ::
          List.map
            (fun pair =>
              FaithfulDiagonalPairMapMachineSymbol.out pair)
            (List.map PairCodeSymbol.left rest ++
              PairCodeSymbol.separator ::
                PairCodeSymbol.right code ::
                  List.map PairCodeSymbol.right rest)
      congr
      have hleft :=
        faithfulDiagonalPairMap_output_left_map rest
      have hright :
          FaithfulDiagonalPairMapMachineSymbol.out
                PairCodeSymbol.separator ::
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.right code) ::
                List.map
                  (fun code =>
                    FaithfulDiagonalPairMapMachineSymbol.out
                      (PairCodeSymbol.right code)) rest =
            List.map
              (fun pair =>
                FaithfulDiagonalPairMapMachineSymbol.out pair)
              (PairCodeSymbol.separator ::
                PairCodeSymbol.right code ::
                  List.map PairCodeSymbol.right rest) := by
        change
          FaithfulDiagonalPairMapMachineSymbol.out
                PairCodeSymbol.separator ::
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.right code) ::
                List.map
                  (fun code =>
                    FaithfulDiagonalPairMapMachineSymbol.out
                      (PairCodeSymbol.right code)) rest =
            FaithfulDiagonalPairMapMachineSymbol.out
                PairCodeSymbol.separator ::
              FaithfulDiagonalPairMapMachineSymbol.out
                (PairCodeSymbol.right code) ::
                List.map
                  (fun pair =>
                    FaithfulDiagonalPairMapMachineSymbol.out pair)
                  (List.map PairCodeSymbol.right rest)
        rw [faithfulDiagonalPairMap_output_right_map rest]
      rw [hleft, hright]
      exact
        (List.map_append
          (f := fun pair =>
            FaithfulDiagonalPairMapMachineSymbol.out pair)
          (l₁ := List.map PairCodeSymbol.left rest)
          (l₂ :=
            PairCodeSymbol.separator ::
              PairCodeSymbol.right code ::
                List.map PairCodeSymbol.right rest)).symm

theorem faithfulDiagonalPairMap_startRaw_moveRight
    (code : ConcreteMachineCodeSymbol)
    (rest : Word ConcreteMachineCodeSymbol) :
    Tape.move Direction.right
      (Tape.write
        (some (FaithfulDiagonalPairMapMachineSymbol.raw code))
        (Tape.input
          (EncodeWord faithfulDiagonalPairMapInputEncode
            (code :: rest)))) =
      faithfulDiagonalPairMapInitScanTape [code] rest := by
  cases rest with
  | nil =>
      rfl
  | cons next suffix =>
      simp [EncodeWord, faithfulDiagonalPairMapInputEncode,
        faithfulDiagonalPairMapInitScanTape, Tape.input,
        Tape.move, Tape.moveRight, Tape.write]

theorem faithful_concrete_diagonal_pair_map_computable :
    FaithfulConcreteDiagonalPairMapComputable := by
  unfold FaithfulConcreteDiagonalPairMapComputable
    FaithfulTuringComputable FaithfulComputesFunction ComputesFunction
  refine
    ⟨ FaithfulDiagonalPairMapMachineSymbol
    , FaithfulDiagonalPairMapMachineState
    , FaithfulConcreteDiagonalPairMapMachine
    , faithfulDiagonalPairMapInputEncode
    , faithfulDiagonalPairMapOutputEncode
    , ?_ ⟩
  refine
    ⟨ faithfulDiagonalPairMapInputEncode_injective
    , faithfulDiagonalPairMapOutputEncode_injective
    , ?_ ⟩
  intro w
  cases w with
  | nil =>
      let finalTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.out
              PairCodeSymbol.separator))
            (Tape.input
              (EncodeWord faithfulDiagonalPairMapInputEncode
                ([] : Word ConcreteMachineCodeSymbol))))
      refine
        ⟨ faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.halt finalTape
        , ?_, rfl, ?_ ⟩
      · refine
          TuringMachine.Computes.step
            (d := faithfulDiagonalPairMapConfig
              FaithfulDiagonalPairMapMachineState.halt finalTape)
            (TuringMachine.Step.mk
              (write := some (FaithfulDiagonalPairMapMachineSymbol.out
                PairCodeSymbol.separator))
              (dir := Direction.right)
              (nextState := FaithfulDiagonalPairMapMachineState.halt)
              ?_)
            (TuringMachine.Computes.refl _)
        rfl
      · change Tape.normalizedOutput finalTape =
          EncodeWord faithfulDiagonalPairMapOutputEncode
            (ConcreteDiagonalPairMap
              ([] : Word ConcreteMachineCodeSymbol))
        simp [finalTape, ConcreteDiagonalPairMap,
          PairCodeSymbol.diagonalMap, PairCodeSymbol.encodePair,
          EncodeWord, Tape.input, Tape.blank, Tape.write, Tape.move,
          Tape.moveRight,
          Tape.normalizedOutput, Tape.cells]
        change
          [FaithfulDiagonalPairMapMachineSymbol.out
            PairCodeSymbol.separator] =
          [FaithfulDiagonalPairMapMachineSymbol.out
            PairCodeSymbol.separator]
        rfl
  | cons code rest =>
      let startNextTape :=
        Tape.move Direction.right
          (Tape.write
            (some (FaithfulDiagonalPairMapMachineSymbol.raw code))
            (Tape.input
              (EncodeWord faithfulDiagonalPairMapInputEncode
                (code :: rest))))
      let returnRev : Word ConcreteMachineCodeSymbol :=
        List.append rest.reverse [code]
      refine
        ⟨ faithfulDiagonalPairMapConfig
            FaithfulDiagonalPairMapMachineState.halt
            (faithfulDiagonalPairMapHaltTape (code :: rest))
        , ?_, rfl, ?_ ⟩
      · refine
          TuringMachine.Computes.step
            (d := faithfulDiagonalPairMapConfig
              FaithfulDiagonalPairMapMachineState.initScan startNextTape)
            (TuringMachine.Step.mk
              (write := some
                (FaithfulDiagonalPairMapMachineSymbol.raw code))
              (dir := Direction.right)
              (nextState := FaithfulDiagonalPairMapMachineState.initScan)
              ?_)
            ?_
        · rfl
        · have hstart :
              startNextTape =
                faithfulDiagonalPairMapInitScanTape [code] rest := by
            simpa [startNextTape]
              using faithfulDiagonalPairMap_startRaw_moveRight code rest
          rw [hstart]
          refine
            TuringMachine.computes_trans
              (faithfulDiagonalPairMap_initScan_computes [code] rest)
              ?_
          refine
            TuringMachine.computes_trans
              (by
                simpa [returnRev]
                  using
                    faithfulDiagonalPairMap_rewind_computes returnRev [])
              ?_
          simpa [returnRev, List.reverse_append, List.append_assoc]
            using
              faithfulDiagonalPairMap_process_computes
                ([] : Word ConcreteMachineCodeSymbol) (code :: rest)
      · exact faithfulDiagonalPairMap_haltTape_normalized (code :: rest)

theorem concrete_diagonal_pair_map_computable_of_faithful :
    ConcreteDiagonalPairMapComputable :=
  faithfulTuringComputable_to_turingComputable
    faithful_concrete_diagonal_pair_map_computable

end Computability
end FoC
