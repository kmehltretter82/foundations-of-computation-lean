import FoC.Computability.Coding
import FoC.Computability.Encoding

set_option doc.verso true

namespace FoC
namespace Book
namespace Chapter05
namespace Section03

/-!
# Chapter 5, Section 5.3: The Limits of Computation

This section formalizes the diagonal and halting-problem statements that mark
the limits of computation. The definitions are book-facing wrappers over
{module}`FoC.Computability.Undecidable`,
{module}`FoC.Computability.Coding`, and
{module}`FoC.Computability.Encoding`, with languages represented as predicates
on encoded words.

The page supplies a concrete pair-code alphabet for halting-problem reductions.
It also exposes the first concrete machine-description syntax and interpreter.
Universal-machine execution is still relative to a later proof that this
interpreter can itself be implemented by a concrete machine.

The structure mirrors the standard textbook argument but keeps the implementation
boundary visible. Abstract decoder and diagonalization theorems are proved in
full generality. Concrete code words, machine descriptions, pair encodings, and
interpreter semantics are present. The final step, a single finite universal
machine implementing the decoder relation, remains an explicit construction
target rather than an implicit assumption.
-/

open Languages
open Computability

/-!
## Undecidability Vocabulary

The first definitions name non-computable functions, non-acceptable languages,
undecidable languages, reductions, diagonal languages, universal decoders, and
halting-problem variants.

The wrappers distinguish two kinds of impossibility. An undecidable language
has no total decider. A non-acceptable language has no recognizer at all. The
diagonal languages are the standard tools for proving such statements.

The concrete definitions in this group are intentionally low-level: they expose
machine code symbols, description encoders and decoders, well-formed transition
tables, interpreter configurations, and description-backed self-halting and
pair-halting languages. This gives later construction work a precise target.
-/

def NonComputableStringFunction (f : Word input -> Word output) : Prop :=
  NonComputableFunction f

def NonTuringAcceptableLanguage (L : Language alpha) : Prop :=
  NonAcceptableLanguage L

def UndecidableTuringLanguage (L : Language alpha) : Prop :=
  UndecidableLanguage L

def RecursiveTuringLanguage (L : Language alpha) : Prop :=
  Recursive L

def RecursivelyEnumerableTuringLanguage (L : Language alpha) : Prop :=
  RecursivelyEnumerable L

def DecidableToAcceptableConstruction (alpha : Type u) : Prop :=
  DecidableToAcceptablePrinciple alpha

def TuringDecidableReduction
    (L : Language input) (K : Language output) : Prop :=
  DecidableReduction L K

def TuringAcceptableReduction
    (L : Language input) (K : Language output) : Prop :=
  AcceptableReduction L K

def TuringDiagonalLanguage (acceptsSelf : Word code -> Prop) : Language code :=
  DiagonalLanguage acceptsSelf

def TuringDecoderRecognizes
    (decodeAccepts : Word code -> Word code -> Prop)
    (machine : Word code) (L : Language code) : Prop :=
  DecoderRecognizes decodeAccepts machine L

def TuringSelfDiagonalLanguage
    (decodeAccepts : Word code -> Word code -> Prop) : Language code :=
  SelfDiagonalLanguage decodeAccepts

def TuringDecoderUniversalForAcceptableLanguages
    (decodeAccepts : Word code -> Word code -> Prop) : Prop :=
  DecoderUniversalForAcceptableLanguages decodeAccepts

def TuringDecoderUniversalForAllLanguages
    (decodeAccepts : Word code -> Word code -> Prop) : Prop :=
  DecoderUniversalForAllLanguages decodeAccepts

def TuringHaltingProblem (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language code :=
  HaltingProblem haltsOnCodeInput

def TuringPairHaltingProblem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language pairSymbol :=
  PairHaltingProblem encodePair haltsOnCodeInput

def TuringSelfHaltingLanguage
    (haltsOnCodeInput : Word code -> Word code -> Prop) : Language code :=
  SelfHaltingLanguage haltsOnCodeInput

def TuringSelfHaltingPairLanguage
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language pairSymbol :=
  SelfHaltingPairLanguage encodePair haltsOnCodeInput

def DiagonalPairDecidablePreimageConstruction
    (encodePair : Word code -> Word code -> Word pairSymbol) : Prop :=
  DiagonalPairDecidablePreimagePrinciple encodePair

def TuringWordPreimageLanguage
    (map : Word input -> Word output)
    (L : Language output) : Language input :=
  WordPreimageLanguage map L

def TuringDecidablePreimageConstruction
    (map : Word input -> Word output) : Prop :=
  DecidablePreimagePrinciple map

def ComputableMapDecidablePreimageConstruction
    (input : Type u) (output : Type v) : Prop :=
  ComputableMapDecidablePreimagePrinciple input output

def TuringComputableWordMap (map : Word input -> Word output) : Prop :=
  TuringComputable map

def TuringPairEncodingInjective
    (encodePair : Word code -> Word code -> Word pairSymbol) : Prop :=
  PairEncodingInjective encodePair

def TuringDiagonalPairMap
    (encodePair : Word code -> Word code -> Word pairSymbol) :
    Word code -> Word pairSymbol :=
  DiagonalPairMap encodePair

/-!
The concrete alphabet below is the file's current machine-code model. It
provides pair encodings, finite code symbols, machine descriptions, decoders,
interpreter configurations, and the encoded self-halting languages used by the
later reduction theorems.
-/

def ConcretePairCodeSymbol (code : Type u) : Type u :=
  PairCodeSymbol code

def ConcretePairEncoding (left right : Word code) :
    Word (ConcretePairCodeSymbol code) :=
  PairCodeSymbol.encodePair left right

def ConcreteDiagonalPairMap (w : Word code) :
    Word (ConcretePairCodeSymbol code) :=
  PairCodeSymbol.diagonalMap w

def ConcreteMachineCodeSymbol : Type :=
  MachineCodeSymbol

def ConcreteDiagonalPairMapComputable : Prop :=
  TuringComputableWordMap
    (ConcreteDiagonalPairMap :
      Word ConcreteMachineCodeSymbol ->
        Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))

theorem concrete_diagonal_pair_map_empty :
    ConcreteDiagonalPairMap ([] : Word ConcreteMachineCodeSymbol) =
      [PairCodeSymbol.separator] :=
  rfl

def ConcreteMachineCodeSymbolFinite :
    Foundation.FiniteType ConcreteMachineCodeSymbol :=
  MachineCodeSymbol.finite

/-!
The next declarations give a concrete finite machine witness for the diagonal
pair map under the current {name}`TuringComputable` interface. That interface permits
non-injective output encodings, so the machine below computes the encoded
diagonal-pair word by mapping every left tag, separator, and right tag to a
single output marker. The proof is still operational: the machine scans the
input, writes one separator marker, converts each raw input cell into an output
marker, appends one marker for the matching right component, and then halts.
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

theorem concrete_diagonal_pair_map_computable :
    ConcreteDiagonalPairMapComputable := by
  unfold ConcreteDiagonalPairMapComputable
    TuringComputableWordMap TuringComputable ComputesFunction
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

def ConcreteMachineTransition : Type :=
  TransitionDescription

def ConcreteMachineDescription : Type :=
  MachineDescription

def ConcreteMachineWellFormed (D : ConcreteMachineDescription) : Prop :=
  MachineDescription.WellFormed D

def ConcreteMachineEncode (D : ConcreteMachineDescription) :
    Word ConcreteMachineCodeSymbol :=
  MachineDescription.encodeDescription D

def ConcreteMachineDecode (w : Word ConcreteMachineCodeSymbol) :
    Option ConcreteMachineDescription :=
  MachineDescription.decodeDescription w

def ConcreteMachineConfiguration : Type :=
  MachineDescription.Configuration

def ConcreteMachineInitial (D : ConcreteMachineDescription)
    (w : Word Bool) : ConcreteMachineConfiguration :=
  D.initial w

def ConcreteMachineStep (D : ConcreteMachineDescription)
    (c : ConcreteMachineConfiguration) :
    Option ConcreteMachineConfiguration :=
  D.stepConfig c

def ConcreteMachineRunConfig (D : ConcreteMachineDescription)
    (n : Nat) (c : ConcreteMachineConfiguration) :
    ConcreteMachineConfiguration :=
  D.runConfig n c

def ConcreteMachineHaltsOnInput (D : ConcreteMachineDescription)
    (w : Word Bool) : Prop :=
  D.HaltsOnInput w

def ConcreteMachineEncodeCodeInput
    (input : Word ConcreteMachineCodeSymbol) : Word Bool :=
  MachineDescription.encodeCodeWordAsInput input

def ConcreteMachineCodeAccepts
    (machine input : Word ConcreteMachineCodeSymbol) : Prop :=
  MachineDescription.CodeAccepts machine input

def ConcreteMachineCodeAcceptedLanguage
    (machine : Word ConcreteMachineCodeSymbol) :
    Language ConcreteMachineCodeSymbol :=
  MachineDescription.CodeAcceptedLanguage machine

def ConcreteMachineEncodedInputLanguage
    (D : ConcreteMachineDescription) :
    Language ConcreteMachineCodeSymbol :=
  MachineDescription.EncodedInputLanguage D

def ConcreteMachineSelfHaltingLanguage :
    Language ConcreteMachineCodeSymbol :=
  TuringSelfHaltingLanguage ConcreteMachineCodeAccepts

def ConcreteMachinePairHaltingProblem :
    Language (ConcretePairCodeSymbol ConcreteMachineCodeSymbol) :=
  TuringPairHaltingProblem
    (ConcretePairEncoding :
      Word ConcreteMachineCodeSymbol ->
        Word ConcreteMachineCodeSymbol ->
          Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    ConcreteMachineCodeAccepts

def ConcreteMachineDiagonalPairPreimageLanguage :
    Language ConcreteMachineCodeSymbol :=
  TuringWordPreimageLanguage
    (ConcreteDiagonalPairMap :
      Word ConcreteMachineCodeSymbol ->
        Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    ConcreteMachinePairHaltingProblem

def ConcreteMachineDecoderUniversalForAcceptableLanguages : Prop :=
  TuringDecoderUniversalForAcceptableLanguages ConcreteMachineCodeAccepts

def ConcreteMachineToTuringMachine (D : ConcreteMachineDescription) :
    TuringMachine Bool (Fin (D.stateCount + 1)) :=
  D.toTuringMachine

def UniversalTuringMachineSpec
    (universal : TuringMachine symbol state)
    (decodeAccepts : Word symbol -> Word symbol -> Prop) : Prop :=
  UniversalMachineSpec universal decodeAccepts

def UniversalMachineRowLanguage
    (universal : TuringMachine symbol state)
    (machine : Word symbol) : Language symbol :=
  fun input => TuringMachine.HaltsOnInput universal
    (Languages.Word.Concat machine input)

def UniversalMachineRowsCoverAcceptableLanguages
    (universal : TuringMachine symbol state) : Prop :=
  forall L : Language symbol, TuringAcceptable L ->
    exists machine : Word symbol,
      Language.Equal (UniversalMachineRowLanguage universal machine) L

def ConcreteUniversalMachineSpec
    (universal : TuringMachine ConcreteMachineCodeSymbol state) : Prop :=
  UniversalTuringMachineSpec universal ConcreteMachineCodeAccepts

def ConcreteUniversalMachineRowsCoverAcceptableLanguages
    (universal : TuringMachine ConcreteMachineCodeSymbol state) : Prop :=
  UniversalMachineRowsCoverAcceptableLanguages universal

/-!
**Reductions and Closure.**

Undecidability and non-acceptability are transported by equality and by the
appropriate reduction notions. Complement theorems record that decidability
and undecidability are symmetric under language complement.

A reduction packages the idea "if the target problem were solvable, then the
source problem would be solvable." Therefore an impossible source problem
transfers impossibility to the target.

The section uses two reduction strengths. Decidable reductions are enough for
undecidability transfer. Acceptable reductions are used when the conclusion is
non-acceptability. The pair-halting results later specialize these general
transfer principles to concrete diagonal pair encodings.
-/

theorem undecidable_of_not_decidable {L : Language alpha}
    (h : ¬ TuringDecidable L) : UndecidableTuringLanguage L :=
  Computability.undecidable_of_not_decidable h

theorem undecidable_language_of_equal {L K : Language alpha}
    (h : UndecidableTuringLanguage L) (hEq : Language.Equal L K) :
    UndecidableTuringLanguage K :=
  Computability.undecidable_of_equal h hEq

theorem undecidable_language_complement {L : Language alpha}
    (h : UndecidableTuringLanguage L) :
    UndecidableTuringLanguage (Language.Compl L) :=
  Computability.undecidable_complement h

theorem undecidable_language_of_undecidable_complement {L : Language alpha}
    (h : UndecidableTuringLanguage (Language.Compl L)) :
    UndecidableTuringLanguage L :=
  Computability.undecidable_of_complement h

theorem undecidable_language_complement_iff {L : Language alpha} :
    UndecidableTuringLanguage (Language.Compl L) <-> UndecidableTuringLanguage L :=
  Computability.undecidable_complement_iff

theorem decidable_reduction_refl (L : Language alpha) :
    TuringDecidableReduction L L :=
  Computability.decidableReduction_refl L

theorem decidable_reduction_trans
    {L : Language alpha} {K : Language beta} {H : Language gamma}
    (hLK : TuringDecidableReduction L K)
    (hKH : TuringDecidableReduction K H) :
    TuringDecidableReduction L H :=
  Computability.decidableReduction_trans hLK hKH

theorem undecidable_of_decidable_reduction
    {L : Language alpha} {K : Language beta}
    (hred : TuringDecidableReduction L K)
    (hL : UndecidableTuringLanguage L) :
    UndecidableTuringLanguage K :=
  Computability.undecidable_of_decidableReduction hred hL

theorem decidable_reduction_complement
    {L : Language alpha} {K : Language beta}
    (h : TuringDecidableReduction L K) :
    TuringDecidableReduction (Language.Compl L) (Language.Compl K) :=
  Computability.decidableReduction_complement h

theorem not_acceptable_of_contradiction {L : Language alpha}
    (h : TuringAcceptable L -> False) : NonTuringAcceptableLanguage L :=
  Computability.not_acceptable_of_diagonal_contradiction h

theorem non_acceptable_language_of_equal {L K : Language alpha}
    (h : NonTuringAcceptableLanguage L) (hEq : Language.Equal L K) :
    NonTuringAcceptableLanguage K :=
  Computability.not_acceptable_of_equal h hEq

theorem acceptable_reduction_refl (L : Language alpha) :
    TuringAcceptableReduction L L :=
  Computability.acceptableReduction_refl L

theorem acceptable_reduction_trans
    {L : Language alpha} {K : Language beta} {H : Language gamma}
    (hLK : TuringAcceptableReduction L K)
    (hKH : TuringAcceptableReduction K H) :
    TuringAcceptableReduction L H :=
  Computability.acceptableReduction_trans hLK hKH

theorem non_acceptable_of_acceptable_reduction
    {L : Language alpha} {K : Language beta}
    (hred : TuringAcceptableReduction L K)
    (hL : NonTuringAcceptableLanguage L) :
    NonTuringAcceptableLanguage K :=
  Computability.not_acceptable_of_acceptableReduction hred hL

theorem non_computable_function_of_pointwise_equal
    {f g : Word input -> Word output}
    (h : NonComputableStringFunction f) (hfg : forall w, f w = g w) :
    NonComputableStringFunction g :=
  Computability.nonComputableFunction_of_pointwise_equal h hfg

theorem decoder_recognizes_of_equal
    {decodeAccepts : Word code -> Word code -> Prop}
    {machine : Word code} {L K : Language code}
    (h : TuringDecoderRecognizes decodeAccepts machine L)
    (hEq : Language.Equal L K) :
    TuringDecoderRecognizes decodeAccepts machine K :=
  Computability.decoderRecognizes_of_equal h hEq

/-!
**Diagonalization.**

The diagonal language differs from every listed row. If a decoder were
universal for all languages, the self-diagonal language would be one of its
rows, contradicting the diagonal theorem.

The construction flips the answer on the diagonal: at code {lit}`w`, it disagrees
with what the {lit}`w`-th decoded machine says about {lit}`w`. No row can therefore be
the diagonal language.

This block is intentionally abstract. It does not depend on a particular
machine encoding, so it cleanly separates the mathematical contradiction from
the engineering task of implementing a universal decoder.
-/

theorem diagonal_language_not_self_recognized (acceptsSelf : Word code -> Prop) :
    ¬ forall w : Word code,
      acceptsSelf w <-> w ∈ TuringDiagonalLanguage acceptsSelf :=
  Computability.diagonal_not_self_recognized acceptsSelf

theorem decoder_cannot_recognize_self_diagonal
    (decodeAccepts : Word code -> Word code -> Prop) :
    ¬ exists machine : Word code,
      TuringDecoderRecognizes decodeAccepts machine
        (TuringSelfDiagonalLanguage decodeAccepts) :=
  Computability.decoder_cannot_recognize_self_diagonal decodeAccepts

theorem decoder_row_not_self_diagonal
    (decodeAccepts : Word code -> Word code -> Prop)
    (machine : Word code) :
    ¬ TuringDecoderRecognizes decodeAccepts machine
      (TuringSelfDiagonalLanguage decodeAccepts) :=
  Computability.decoder_row_not_self_diagonal decodeAccepts machine

theorem self_diagonal_missing_from_decoder_rows
    (decodeAccepts : Word code -> Word code -> Prop) :
    exists L : Language code,
      ¬ exists machine : Word code,
        TuringDecoderRecognizes decodeAccepts machine L :=
  Computability.self_diagonal_missing_from_decoder_rows decodeAccepts

theorem decoder_not_universal_for_all_languages
    (decodeAccepts : Word code -> Word code -> Prop) :
    ¬ TuringDecoderUniversalForAllLanguages decodeAccepts :=
  Computability.decoder_not_universal_for_all_languages decodeAccepts

theorem self_diagonal_not_acceptable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    NonTuringAcceptableLanguage
      (TuringSelfDiagonalLanguage decodeAccepts) :=
  Computability.self_diagonal_not_acceptable_if_decoder_universal huniv

theorem exists_nonacceptable_language_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    exists L : Language code, NonTuringAcceptableLanguage L :=
  Computability.exists_nonacceptable_language_if_decoder_universal huniv

/-!
**Self-Halting and the Halting Problem.**

The self-diagonal language is the complement of self-halting. Under a universal
decoder, this yields the standard undecidability and non-RE complement results,
then relates self-halting to pair-encoded halting problems.

Self-halting asks whether a machine halts on its own code. The ordinary
two-input halting problem is at least as hard because self-halting is the
preimage obtained by feeding the same code into both slots.

The concrete pair-code alphabet makes that preimage statement exact for encoded
machine descriptions. The remaining computability/preimage construction
theorems name the compiler and universal-runner facts required to turn the
abstract reduction into the final concrete halting-problem theorem.
-/

theorem self_diagonal_equal_complement_self_halting
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language.Equal (TuringSelfDiagonalLanguage haltsOnCodeInput)
      (Language.Compl (TuringSelfHaltingLanguage haltsOnCodeInput)) :=
  Computability.selfDiagonal_equal_compl_selfHalting haltsOnCodeInput

theorem complement_self_halting_not_acceptable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    NonTuringAcceptableLanguage
      (Language.Compl (TuringSelfHaltingLanguage decodeAccepts)) :=
  Computability.compl_selfHalting_not_acceptable_if_decoder_universal huniv

theorem complement_self_halting_not_recursively_enumerable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    ¬ RecursivelyEnumerableTuringLanguage
      (Language.Compl (TuringSelfHaltingLanguage decodeAccepts)) :=
  Computability.compl_selfHalting_not_recursivelyEnumerable_if_decoder_universal
    huniv

theorem self_halting_not_recursive_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    ¬ RecursiveTuringLanguage (TuringSelfHaltingLanguage decodeAccepts) :=
  Computability.selfHalting_not_recursive_if_decoder_universal
    haccept huniv

theorem self_halting_undecidable_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage (TuringSelfHaltingLanguage decodeAccepts) :=
  Computability.selfHalting_undecidable_if_decoder_universal
    haccept huniv

theorem self_halting_re_not_recursive_and_complement_not_re_if_decoder_universal
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts)
    (hself : RecursivelyEnumerableTuringLanguage
      (TuringSelfHaltingLanguage decodeAccepts)) :
    RecursivelyEnumerableTuringLanguage
        (TuringSelfHaltingLanguage decodeAccepts) ∧
      ¬ RecursiveTuringLanguage (TuringSelfHaltingLanguage decodeAccepts) ∧
        ¬ RecursivelyEnumerableTuringLanguage
          (Language.Compl (TuringSelfHaltingLanguage decodeAccepts)) :=
  Computability.selfHalting_re_not_recursive_and_compl_not_re_if_decoder_universal
    haccept huniv hself

/-!
These membership lemmas unfold the halting-problem encodings. They make the
two-input problem explicit either as concatenation or as a supplied pair encoder,
then identify self-halting as the diagonal preimage of pair halting.
-/

theorem halting_problem_mem
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    (encodedPair : Word code) :
    encodedPair ∈ TuringHaltingProblem haltsOnCodeInput <->
      exists machine input : Word code,
        encodedPair = Languages.Word.Concat machine input ∧
          haltsOnCodeInput machine input :=
  Computability.haltingProblem_mem haltsOnCodeInput encodedPair

theorem pair_halting_problem_mem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    (encodedPair : Word pairSymbol) :
    encodedPair ∈
        TuringPairHaltingProblem encodePair haltsOnCodeInput <->
      exists machine input : Word code,
        encodedPair = encodePair machine input ∧
          haltsOnCodeInput machine input :=
  Computability.pairHaltingProblem_mem
    encodePair haltsOnCodeInput encodedPair

theorem halting_problem_equal_concat_pair_halting_problem
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language.Equal (TuringHaltingProblem haltsOnCodeInput)
      (TuringPairHaltingProblem
        (fun machine input : Word code => Languages.Word.Concat machine input)
        haltsOnCodeInput) :=
  Computability.haltingProblem_equal_pairHaltingProblem_concat
    haltsOnCodeInput

theorem halting_problem_contains_encoded_halting_pair
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    {machine input : Word code}
    (hhalts : haltsOnCodeInput machine input) :
    Languages.Word.Concat machine input ∈
      TuringHaltingProblem haltsOnCodeInput :=
  Computability.haltingProblem_contains_encoded_halting_pair
    haltsOnCodeInput hhalts

theorem pair_halting_problem_contains_encoded_halting_pair
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    {machine input : Word code}
    (hhalts : haltsOnCodeInput machine input) :
    encodePair machine input ∈
      TuringPairHaltingProblem encodePair haltsOnCodeInput :=
  Computability.pairHaltingProblem_contains_encoded_halting_pair
    encodePair haltsOnCodeInput hhalts

theorem halting_problem_pair_elim
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    {encodedPair : Word code}
    (h : encodedPair ∈ TuringHaltingProblem haltsOnCodeInput) :
    exists machine input : Word code,
      encodedPair = Languages.Word.Concat machine input ∧
        haltsOnCodeInput machine input :=
  Computability.haltingProblem_pair_elim h

theorem pair_halting_problem_pair_elim
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    {encodedPair : Word pairSymbol}
    (h : encodedPair ∈
      TuringPairHaltingProblem encodePair haltsOnCodeInput) :
    exists machine input : Word code,
      encodedPair = encodePair machine input ∧
        haltsOnCodeInput machine input :=
  Computability.pairHaltingProblem_pair_elim h

theorem self_halting_pair_language_mem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop)
    (encodedPair : Word pairSymbol) :
    encodedPair ∈
        TuringSelfHaltingPairLanguage encodePair haltsOnCodeInput <->
      exists machine : Word code,
        encodedPair = encodePair machine machine ∧
          haltsOnCodeInput machine machine :=
  Computability.selfHaltingPairLanguage_mem
    encodePair haltsOnCodeInput encodedPair

theorem self_halting_pair_language_subset_pair_halting_problem
    (encodePair : Word code -> Word code -> Word pairSymbol)
    (haltsOnCodeInput : Word code -> Word code -> Prop) :
    Language.Subset
      (TuringSelfHaltingPairLanguage encodePair haltsOnCodeInput)
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  Computability.selfHaltingPairLanguage_subset_pairHaltingProblem
    encodePair haltsOnCodeInput

theorem word_preimage_language_mem
    (map : Word input -> Word output)
    (L : Language output)
    (w : Word input) :
    w ∈ TuringWordPreimageLanguage map L <-> map w ∈ L :=
  Computability.wordPreimageLanguage_mem map L w

theorem diagonal_pair_preimage_pair_halting_equal_self_halting
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hinj : TuringPairEncodingInjective encodePair) :
    Language.Equal
      (TuringWordPreimageLanguage
        (TuringDiagonalPairMap encodePair)
        (TuringPairHaltingProblem encodePair haltsOnCodeInput))
      (TuringSelfHaltingLanguage haltsOnCodeInput) :=
  Computability.diagonalPairMap_preimage_pairHalting_equal_selfHalting
    (encodePair := encodePair)
    (haltsOnCodeInput := haltsOnCodeInput)
    hinj

/-!
The next facts specialize the abstract decoder story to concrete machine
descriptions. Encoding then decoding a description is exact, and a universal
machine specification is phrased as an iff between universal-machine halting and
the description-level acceptance relation.
-/

theorem concrete_machine_decode_encode
    (D : ConcreteMachineDescription) :
    ConcreteMachineDecode (ConcreteMachineEncode D) = some D :=
  MachineDescription.decodeDescription_encodeDescription D

theorem concrete_machine_code_accepts_encode_description_iff
    (D : ConcreteMachineDescription)
    (input : Word ConcreteMachineCodeSymbol) :
    ConcreteMachineCodeAccepts (ConcreteMachineEncode D) input <->
      ConcreteMachineHaltsOnInput D
        (ConcreteMachineEncodeCodeInput input) :=
  MachineDescription.codeAccepts_encodeDescription_iff D input

theorem concrete_machine_encoded_description_accepts
    {D : ConcreteMachineDescription}
    {input : Word ConcreteMachineCodeSymbol}
    (h : ConcreteMachineHaltsOnInput D
      (ConcreteMachineEncodeCodeInput input)) :
    ConcreteMachineCodeAccepts (ConcreteMachineEncode D) input :=
  (concrete_machine_code_accepts_encode_description_iff D input).mpr h

theorem concrete_machine_encoded_description_accepts_elim
    {D : ConcreteMachineDescription}
    {input : Word ConcreteMachineCodeSymbol}
    (h : ConcreteMachineCodeAccepts (ConcreteMachineEncode D) input) :
    ConcreteMachineHaltsOnInput D
      (ConcreteMachineEncodeCodeInput input) :=
  (concrete_machine_code_accepts_encode_description_iff D input).mp h

theorem concrete_machine_encoded_description_recognizes_input_language
    (D : ConcreteMachineDescription) :
    TuringDecoderRecognizes ConcreteMachineCodeAccepts
      (ConcreteMachineEncode D)
      (ConcreteMachineEncodedInputLanguage D) := by
  intro input
  exact concrete_machine_code_accepts_encode_description_iff D input

theorem concrete_universal_machine_spec_accepts_iff
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalMachineSpec universal)
    (machine input : Word ConcreteMachineCodeSymbol) :
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat machine input) <->
        ConcreteMachineCodeAccepts machine input :=
  hspec machine input

theorem concrete_universal_machine_halts_on_encoded_description_iff
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalMachineSpec universal)
    (D : ConcreteMachineDescription)
    (input : Word ConcreteMachineCodeSymbol) :
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat (ConcreteMachineEncode D) input) <->
        ConcreteMachineHaltsOnInput D
          (ConcreteMachineEncodeCodeInput input) :=
  Iff.trans
    (concrete_universal_machine_spec_accepts_iff
      hspec (ConcreteMachineEncode D) input)
    (concrete_machine_code_accepts_encode_description_iff D input)

theorem concrete_universal_machine_row_language_equal_code_accepted_language
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalMachineSpec universal)
    (machine : Word ConcreteMachineCodeSymbol) :
    Language.Equal
      (UniversalMachineRowLanguage universal machine)
      (ConcreteMachineCodeAcceptedLanguage machine) :=
  concrete_universal_machine_spec_accepts_iff hspec machine

theorem concrete_universal_machine_row_language_equal_encoded_input_language
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalMachineSpec universal)
    (D : ConcreteMachineDescription) :
    Language.Equal
      (UniversalMachineRowLanguage universal (ConcreteMachineEncode D))
      (ConcreteMachineEncodedInputLanguage D) :=
  concrete_universal_machine_halts_on_encoded_description_iff hspec D

theorem concrete_machine_compiled_transition_of_lookup
    {D : ConcreteMachineDescription}
    {source : Nat} {read : Option Bool}
    {t : ConcreteMachineTransition}
    (hsource : source < D.stateCount + 1)
    (hlookup : D.lookupTransition source read = some t) :
    (ConcreteMachineToTuringMachine D).transition
      (D.stateOfNat source) read =
        some (t.write, t.move, D.stateOfNat t.target) :=
  MachineDescription.toTuringMachine_transition_of_lookup
    hsource hlookup

theorem concrete_machine_turing_step_of_interpreter_step
    {D : ConcreteMachineDescription}
    {c d : ConcreteMachineConfiguration}
    (hsource : c.state < D.stateCount + 1)
    (hstep : ConcreteMachineStep D c = some d) :
    TuringMachine.Step (ConcreteMachineToTuringMachine D)
      (D.toTMConfig c) (D.toTMConfig d) :=
  MachineDescription.toTuringMachine_step_of_stepConfig
    hsource hstep

/-!
Concrete pair codes discharge the injectivity part of diagonal preimages. The
remaining preimage principles say when a decider for pair halting would induce a
decider for self-halting by composing with the diagonal map.
-/

def concrete_pair_code_symbol_finite
    (h : Foundation.FiniteType code) :
    Foundation.FiniteType (ConcretePairCodeSymbol code) :=
  PairCodeSymbol.finite h

theorem concrete_pair_encoding_injective :
    TuringPairEncodingInjective
      (ConcretePairEncoding :
        Word code -> Word code -> Word (ConcretePairCodeSymbol code)) :=
  PairCodeSymbol.encodePair_injective

theorem concrete_diagonal_pair_preimage_pair_halting_equal_self_halting
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    Language.Equal
      (TuringWordPreimageLanguage
        (ConcreteDiagonalPairMap :
          Word code -> Word (ConcretePairCodeSymbol code))
        (TuringPairHaltingProblem
          (ConcretePairEncoding :
            Word code -> Word code -> Word (ConcretePairCodeSymbol code))
          haltsOnCodeInput))
      (TuringSelfHaltingLanguage haltsOnCodeInput) :=
  PairCodeSymbol.diagonalMap_preimage_pairHalting_equal_selfHalting

theorem concrete_machine_diagonal_pair_preimage_pair_halting_equal_self_halting :
    Language.Equal
      ConcreteMachineDiagonalPairPreimageLanguage
      ConcreteMachineSelfHaltingLanguage :=
  concrete_diagonal_pair_preimage_pair_halting_equal_self_halting
    (haltsOnCodeInput := ConcreteMachineCodeAccepts)

theorem diagonal_pair_map_mem_pair_halting_iff_self_halting
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (machine : Word code) :
    (TuringDiagonalPairMap encodePair machine) ∈
        TuringPairHaltingProblem encodePair haltsOnCodeInput <->
      machine ∈ TuringSelfHaltingLanguage haltsOnCodeInput := by
  change machine ∈
      TuringWordPreimageLanguage
        (TuringDiagonalPairMap encodePair)
        (TuringPairHaltingProblem encodePair haltsOnCodeInput) <->
    machine ∈ TuringSelfHaltingLanguage haltsOnCodeInput
  exact diagonal_pair_preimage_pair_halting_equal_self_halting
    (encodePair := encodePair)
    (haltsOnCodeInput := haltsOnCodeInput)
    hinj
    machine

theorem concrete_diagonal_pair_map_mem_pair_halting_iff_self_halting
    (machine : Word ConcreteMachineCodeSymbol) :
    (ConcreteDiagonalPairMap machine) ∈ ConcreteMachinePairHaltingProblem <->
      machine ∈ ConcreteMachineSelfHaltingLanguage := by
  change machine ∈ ConcreteMachineDiagonalPairPreimageLanguage <->
    machine ∈ ConcreteMachineSelfHaltingLanguage
  exact
    concrete_machine_diagonal_pair_preimage_pair_halting_equal_self_halting
      machine

theorem diagonal_pair_preimage_recursive_iff_self_halting_recursive
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    RecursiveTuringLanguage
        (TuringWordPreimageLanguage
          (TuringDiagonalPairMap encodePair)
          (TuringPairHaltingProblem encodePair haltsOnCodeInput)) <->
      RecursiveTuringLanguage
        (TuringSelfHaltingLanguage haltsOnCodeInput) := by
  constructor
  · intro h
    exact Computability.turing_decidable_of_equal h
      (diagonal_pair_preimage_pair_halting_equal_self_halting
        (encodePair := encodePair)
        (haltsOnCodeInput := haltsOnCodeInput)
        hinj)
  · intro h
    exact Computability.turing_decidable_of_equal h
      (Language.equal_symm
        (diagonal_pair_preimage_pair_halting_equal_self_halting
          (encodePair := encodePair)
          (haltsOnCodeInput := haltsOnCodeInput)
          hinj))

theorem concrete_machine_diagonal_pair_preimage_recursive_iff_self_halting_recursive :
    RecursiveTuringLanguage ConcreteMachineDiagonalPairPreimageLanguage <->
      RecursiveTuringLanguage ConcreteMachineSelfHaltingLanguage := by
  constructor
  · intro h
    exact Computability.turing_decidable_of_equal h
      concrete_machine_diagonal_pair_preimage_pair_halting_equal_self_halting
  · intro h
    exact Computability.turing_decidable_of_equal h
      (Language.equal_symm
        concrete_machine_diagonal_pair_preimage_pair_halting_equal_self_halting)

theorem diagonal_pair_decidable_preimage_construction_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      TuringDecidablePreimageConstruction (TuringDiagonalPairMap encodePair)) :
    DiagonalPairDecidablePreimageConstruction encodePair :=
  Computability.diagonalPairDecidablePreimagePrinciple_of_preimage
    hinj hpreimage

theorem concrete_diagonal_pair_decidable_preimage_construction_of_preimage
    (hpreimage :
      TuringDecidablePreimageConstruction
        (ConcreteDiagonalPairMap :
          Word code -> Word (ConcretePairCodeSymbol code))) :
    DiagonalPairDecidablePreimageConstruction
      (ConcretePairEncoding :
        Word code -> Word code -> Word (ConcretePairCodeSymbol code)) :=
  PairCodeSymbol.diagonalPairDecidablePreimagePrinciple_of_concrete_preimage
    hpreimage

theorem decidable_preimage_construction_of_computable_map_construction
    (hpreimage : ComputableMapDecidablePreimageConstruction input output)
    {map : Word input -> Word output}
    (hcomputable : TuringComputableWordMap map) :
    TuringDecidablePreimageConstruction map :=
  Computability.decidablePreimagePrinciple_of_computableMapPrinciple
    hpreimage hcomputable

theorem diagonal_pair_decidable_preimage_construction_of_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage : ComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable : TuringComputableWordMap (TuringDiagonalPairMap encodePair)) :
    DiagonalPairDecidablePreimageConstruction encodePair :=
  Computability.diagonalPairDecidablePreimagePrinciple_of_computableMapPrinciple
    hinj hpreimage hcomputable

theorem diagonal_pair_decidable_reduction_self_halting_to_pair_halting
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hdiag : DiagonalPairDecidablePreimageConstruction encodePair) :
    TuringDecidableReduction
      (TuringSelfHaltingLanguage haltsOnCodeInput)
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  hdiag haltsOnCodeInput

theorem diagonal_pair_decidable_reduction_self_halting_to_pair_halting_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      TuringDecidablePreimageConstruction (TuringDiagonalPairMap encodePair))
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    TuringDecidableReduction
      (TuringSelfHaltingLanguage haltsOnCodeInput)
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  diagonal_pair_decidable_reduction_self_halting_to_pair_halting
    (diagonal_pair_decidable_preimage_construction_of_preimage
      hinj hpreimage)

theorem diagonal_pair_decidable_reduction_self_halting_to_pair_halting_of_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage : ComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable : TuringComputableWordMap (TuringDiagonalPairMap encodePair))
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    TuringDecidableReduction
      (TuringSelfHaltingLanguage haltsOnCodeInput)
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  diagonal_pair_decidable_reduction_self_halting_to_pair_halting
    (diagonal_pair_decidable_preimage_construction_of_computable_map
      hinj hpreimage hcomputable)

theorem concrete_diagonal_pair_decidable_preimage_construction_of_computable_map
    (hpreimage :
      ComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : ConcreteDiagonalPairMapComputable) :
    DiagonalPairDecidablePreimageConstruction
      (ConcretePairEncoding :
        Word ConcreteMachineCodeSymbol ->
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) := by
  simpa [DiagonalPairDecidablePreimageConstruction,
    ConcretePairEncoding, ConcretePairCodeSymbol, ConcreteDiagonalPairMap,
    ConcreteDiagonalPairMapComputable,
    ComputableMapDecidablePreimageConstruction, TuringComputableWordMap]
    using
      PairCodeSymbol.diagonalPairDecidablePreimagePrinciple_of_concrete_computable_map
        (code := ConcreteMachineCodeSymbol) hpreimage hcomputable

theorem concrete_machine_self_halting_reduces_to_pair_halting_of_preimage
    (hpreimage :
      TuringDecidablePreimageConstruction
        (ConcreteDiagonalPairMap :
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))) :
    TuringDecidableReduction
      ConcreteMachineSelfHaltingLanguage
      ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachineSelfHaltingLanguage, ConcreteMachinePairHaltingProblem]
    using
      diagonal_pair_decidable_reduction_self_halting_to_pair_halting
        (encodePair :=
          (ConcretePairEncoding :
            Word ConcreteMachineCodeSymbol ->
              Word ConcreteMachineCodeSymbol ->
                Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
        (haltsOnCodeInput := ConcreteMachineCodeAccepts)
        (concrete_diagonal_pair_decidable_preimage_construction_of_preimage
          (code := ConcreteMachineCodeSymbol) hpreimage)

theorem concrete_machine_self_halting_reduces_to_pair_halting_of_computable_map
    (hpreimage :
      ComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : ConcreteDiagonalPairMapComputable) :
    TuringDecidableReduction
      ConcreteMachineSelfHaltingLanguage
      ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachineSelfHaltingLanguage, ConcreteMachinePairHaltingProblem]
    using
      diagonal_pair_decidable_reduction_self_halting_to_pair_halting
        (encodePair :=
          (ConcretePairEncoding :
            Word ConcreteMachineCodeSymbol ->
              Word ConcreteMachineCodeSymbol ->
                Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
        (haltsOnCodeInput := ConcreteMachineCodeAccepts)
        (concrete_diagonal_pair_decidable_preimage_construction_of_computable_map
          hpreimage hcomputable)

theorem halting_problem_of_pointwise_iff
    {halts1 halts2 : Word code -> Word code -> Prop}
    (hiff : forall machine input : Word code,
      halts1 machine input <-> halts2 machine input) :
    Language.Equal (TuringHaltingProblem halts1)
      (TuringHaltingProblem halts2) :=
  Computability.haltingProblem_of_pointwise_iff hiff

theorem pair_halting_problem_of_pointwise_iff
    (encodePair : Word code -> Word code -> Word pairSymbol)
    {halts1 halts2 : Word code -> Word code -> Prop}
    (hiff : forall machine input : Word code,
      halts1 machine input <-> halts2 machine input) :
    Language.Equal (TuringPairHaltingProblem encodePair halts1)
      (TuringPairHaltingProblem encodePair halts2) :=
  Computability.pairHaltingProblem_of_pointwise_iff encodePair hiff

/-!
The pair-halting transfer theorems now apply the diagonal preimage argument.
An undecidable self-halting language forces the corresponding pair-halting
language to be undecidable; universal decoders supply the self-halting
undecidability needed for the standard theorem.
-/

theorem pair_halting_undecidable_if_self_halting_undecidable
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hdiag :
      DiagonalPairDecidablePreimageConstruction encodePair)
    (hself :
      UndecidableTuringLanguage
        (TuringSelfHaltingLanguage haltsOnCodeInput)) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  Computability.pairHalting_undecidable_if_selfHalting_undecidable
    hdiag hself

theorem pair_halting_undecidable_if_self_halting_undecidable_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {haltsOnCodeInput : Word code -> Word code -> Prop}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      TuringDecidablePreimageConstruction (TuringDiagonalPairMap encodePair))
    (hself :
      UndecidableTuringLanguage
        (TuringSelfHaltingLanguage haltsOnCodeInput)) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  Computability.pairHalting_undecidable_if_selfHalting_undecidable_of_preimage
    hinj hpreimage hself

theorem pair_halting_undecidable_if_decoder_universal
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hdiag :
      DiagonalPairDecidablePreimageConstruction encodePair)
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair decodeAccepts) :=
  Computability.pairHalting_undecidable_if_decoder_universal
    haccept hdiag huniv

theorem pair_halting_undecidable_if_decoder_universal_of_preimage
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      TuringDecidablePreimageConstruction (TuringDiagonalPairMap encodePair))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair decodeAccepts) :=
  Computability.pairHalting_undecidable_if_decoder_universal_of_preimage
    haccept hinj hpreimage huniv

theorem pair_halting_undecidable_if_decoder_universal_of_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage : ComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable : TuringComputableWordMap (TuringDiagonalPairMap encodePair))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair decodeAccepts) :=
  Computability.pairHalting_undecidable_if_decoder_universal
    haccept
    (diagonal_pair_decidable_preimage_construction_of_computable_map
      hinj hpreimage hcomputable)
    huniv

theorem concrete_pair_halting_undecidable_if_decoder_universal_of_preimage
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hpreimage :
      TuringDecidablePreimageConstruction
        (ConcreteDiagonalPairMap :
          Word code -> Word (ConcretePairCodeSymbol code)))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem
        (ConcretePairEncoding :
          Word code -> Word code -> Word (ConcretePairCodeSymbol code))
        decodeAccepts) :=
  PairCodeSymbol.concretePairHalting_undecidable_if_decoder_universal_of_preimage
    haccept hpreimage huniv

theorem concrete_pair_halting_undecidable_if_decoder_universal_of_computable_map
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hpreimage :
      ComputableMapDecidablePreimageConstruction code (ConcretePairCodeSymbol code))
    (hcomputable :
      TuringComputableWordMap
        (ConcreteDiagonalPairMap :
          Word code -> Word (ConcretePairCodeSymbol code)))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem
        (ConcretePairEncoding :
          Word code -> Word code -> Word (ConcretePairCodeSymbol code))
        decodeAccepts) :=
  PairCodeSymbol.concretePairHalting_undecidable_if_decoder_universal_of_computable_map
    haccept hpreimage hcomputable huniv

/-!
The concrete machine statements instantiate the abstract results with the
machine-code alphabet and description decoder. They remain conditional on the
acceptability principle, universal decoder, and diagonal-map preimage or
computability hypotheses named in their signatures.
-/

theorem concrete_machine_self_halting_undecidable_if_decoder_universal
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    UndecidableTuringLanguage ConcreteMachineSelfHaltingLanguage :=
  self_halting_undecidable_if_decoder_universal
    haccept huniv

theorem concrete_machine_complement_self_halting_not_recursively_enumerable_if_decoder_universal
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    ¬ RecursivelyEnumerableTuringLanguage
      (Language.Compl ConcreteMachineSelfHaltingLanguage) :=
  complement_self_halting_not_recursively_enumerable_if_decoder_universal
    huniv

theorem concrete_machine_pair_halting_undecidable_if_self_halting_undecidable_of_preimage
    (hpreimage :
      TuringDecidablePreimageConstruction
        (ConcreteDiagonalPairMap :
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
    (hself :
      UndecidableTuringLanguage ConcreteMachineSelfHaltingLanguage) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachinePairHaltingProblem]
    using
      pair_halting_undecidable_if_self_halting_undecidable_of_preimage
        (encodePair :=
          (ConcretePairEncoding :
            Word ConcreteMachineCodeSymbol ->
              Word ConcreteMachineCodeSymbol ->
                Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
        (haltsOnCodeInput := ConcreteMachineCodeAccepts)
        concrete_pair_encoding_injective
        hpreimage
        hself

theorem concrete_machine_pair_halting_undecidable_if_self_halting_undecidable_of_computable_map
    (hpreimage :
      ComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : ConcreteDiagonalPairMapComputable)
    (hself :
      UndecidableTuringLanguage ConcreteMachineSelfHaltingLanguage) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem :=
  undecidable_of_decidable_reduction
    (concrete_machine_self_halting_reduces_to_pair_halting_of_computable_map
      hpreimage hcomputable)
    hself

theorem concrete_machine_pair_halting_undecidable_if_decoder_universal_of_preimage
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (hpreimage :
      TuringDecidablePreimageConstruction
        (ConcreteDiagonalPairMap :
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)))
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachinePairHaltingProblem]
    using
      concrete_pair_halting_undecidable_if_decoder_universal_of_preimage
        (code := ConcreteMachineCodeSymbol)
        (decodeAccepts := ConcreteMachineCodeAccepts)
        haccept hpreimage huniv

theorem concrete_machine_pair_halting_undecidable_if_decoder_universal_of_computable_map
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (hpreimage :
      ComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : ConcreteDiagonalPairMapComputable)
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachinePairHaltingProblem]
    using
      concrete_pair_halting_undecidable_if_decoder_universal_of_computable_map
        (code := ConcreteMachineCodeSymbol)
        (decodeAccepts := ConcreteMachineCodeAccepts)
        haccept hpreimage hcomputable huniv

/-!
The universal-machine specification is intentionally small: it only records the
two directions between universal-machine halting on encoded pairs and the
decoder acceptance predicate. Concrete universal machines can instantiate this
interface later.
-/

theorem universal_machine_spec_pair_halts
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts)
    {machine input : Word symbol}
    (hdecode : decodeAccepts machine input) :
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat machine input) :=
  Computability.universalMachineSpec_pair_halts hspec hdecode

theorem universal_machine_spec_pair_decode
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts)
    {machine input : Word symbol}
    (hhalts : TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat machine input)) :
    decodeAccepts machine input :=
  Computability.universalMachineSpec_pair_decode hspec hhalts

theorem universal_machine_spec_decoder_recognizes_row_language
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts)
    (machine : Word symbol) :
    TuringDecoderRecognizes decodeAccepts machine
      (UniversalMachineRowLanguage universal machine) := by
  intro input
  exact (hspec machine input).symm

theorem universal_machine_rows_cover_of_decoder_universal
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts)
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UniversalMachineRowsCoverAcceptableLanguages universal := by
  intro L hL
  cases huniv L hL with
  | intro machine hmachine =>
      exists machine
      intro input
      exact Iff.trans (hspec machine input) (hmachine input)

theorem decoder_universal_of_universal_machine_rows_cover
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts)
    (hrows : UniversalMachineRowsCoverAcceptableLanguages universal) :
    TuringDecoderUniversalForAcceptableLanguages decodeAccepts := by
  intro L hL
  cases hrows L hL with
  | intro machine hmachine =>
      exists machine
      intro input
      exact Iff.trans (hspec machine input).symm (hmachine input)

theorem universal_machine_rows_cover_iff_decoder_universal
    {universal : TuringMachine symbol state}
    {decodeAccepts : Word symbol -> Word symbol -> Prop}
    (hspec : UniversalTuringMachineSpec universal decodeAccepts) :
    UniversalMachineRowsCoverAcceptableLanguages universal <->
      TuringDecoderUniversalForAcceptableLanguages decodeAccepts := by
  constructor
  · exact decoder_universal_of_universal_machine_rows_cover hspec
  · exact universal_machine_rows_cover_of_decoder_universal hspec

theorem concrete_universal_machine_rows_cover_of_decoder_universal
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalMachineSpec universal)
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    ConcreteUniversalMachineRowsCoverAcceptableLanguages universal :=
  universal_machine_rows_cover_of_decoder_universal hspec huniv

theorem concrete_decoder_universal_of_universal_machine_rows_cover
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalMachineSpec universal)
    (hrows : ConcreteUniversalMachineRowsCoverAcceptableLanguages universal) :
    ConcreteMachineDecoderUniversalForAcceptableLanguages :=
  decoder_universal_of_universal_machine_rows_cover hspec hrows

theorem concrete_universal_machine_rows_cover_iff_decoder_universal
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalMachineSpec universal) :
    ConcreteUniversalMachineRowsCoverAcceptableLanguages universal <->
      ConcreteMachineDecoderUniversalForAcceptableLanguages :=
  universal_machine_rows_cover_iff_decoder_universal hspec

/-!
The section's universal-machine and diagonalization theorems require a concrete
encoding of machines as strings.  This module records the formal statement
vocabulary without adding an unproved universal-machine assumption.

Once a concrete universal machine and encoding are supplied, these statements
can be instantiated to recover the usual textbook halting-problem theorems.

This is the current status boundary for Section 5.3. The encoding, interpreter,
compiled-machine simulation, decoder-row wrappers, and pair-code reductions are
formalized. Machine output is now read through normalized tape contents, so
singleton outputs from empty input and Boolean deciders are no longer blocked by
finite tape-window artifacts. The concrete diagonal pair map now has an
explicit finite-machine witness for the current non-injective output-encoding
interface. The remaining concrete work is the finite universal-machine
construction, or a stronger faithful copy-machine theorem if computable string
functions are later refined to require injective encodings.
-/

end Section03
end Chapter05
end Book
end FoC
