import FoC.Computability.Compiler.Core.FiniteRecognizer.Basic

set_option doc.verso true

/-!
# Exact-fuel protected layouts

This module introduces the semantic work layout used by the exact-fuel finite
recognizer runner.  The layout protects the simulated configuration from the
generated-code prefix by moving to an explicit encoded configuration:

- remaining fuel;
- simulated state;
- simulated left context;
- simulated head cell;
- simulated right context.

The module intentionally proves semantic step laws before any concrete
transition table is introduced.
-/

namespace FoC
namespace Computability

open Languages

namespace FiniteRecognizer
namespace ExactFuel

/-- Numeric tag for code symbols inside exact-fuel work layouts. -/
def codeSymbolTag : MachineCodeSymbol -> Nat
  | MachineCodeSymbol.header => 0
  | MachineCodeSymbol.transition => 1
  | MachineCodeSymbol.tick => 2
  | MachineCodeSymbol.done => 3
  | MachineCodeSymbol.blank => 4
  | MachineCodeSymbol.zero => 5
  | MachineCodeSymbol.one => 6
  | MachineCodeSymbol.moveLeft => 7
  | MachineCodeSymbol.moveRight => 8

/-- Partial inverse to {name}`codeSymbolTag`. -/
def decodeCodeSymbolTag : Nat -> Option MachineCodeSymbol
  | 0 => some MachineCodeSymbol.header
  | 1 => some MachineCodeSymbol.transition
  | 2 => some MachineCodeSymbol.tick
  | 3 => some MachineCodeSymbol.done
  | 4 => some MachineCodeSymbol.blank
  | 5 => some MachineCodeSymbol.zero
  | 6 => some MachineCodeSymbol.one
  | 7 => some MachineCodeSymbol.moveLeft
  | 8 => some MachineCodeSymbol.moveRight
  | _ => none

theorem decodeCodeSymbolTag_codeSymbolTag
    (symbol : MachineCodeSymbol) :
    decodeCodeSymbolTag (codeSymbolTag symbol) = some symbol := by
  cases symbol <;> rfl

def optionalCodeSymbolTag : Option MachineCodeSymbol -> Nat
  | none => 0
  | some symbol => codeSymbolTag symbol + 1

def decodeOptionalCodeSymbolTag :
    Nat -> Option (Option MachineCodeSymbol)
  | 0 => some none
  | n + 1 =>
      Option.map some (decodeCodeSymbolTag n)

theorem decodeOptionalCodeSymbolTag_optionalCodeSymbolTag
    (cell : Option MachineCodeSymbol) :
    decodeOptionalCodeSymbolTag (optionalCodeSymbolTag cell) =
      some cell := by
  cases cell with
  | none => rfl
  | some symbol =>
      simp [optionalCodeSymbolTag, decodeOptionalCodeSymbolTag,
        decodeCodeSymbolTag_codeSymbolTag]

def encodeOptionalCodeSymbolAppend
    (cell : Option MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend
    (optionalCodeSymbolTag cell) suffix

theorem encodeOptionalCodeSymbolAppend_none
    (suffix : Word MachineCodeSymbol) :
    encodeOptionalCodeSymbolAppend none suffix =
      MachineDescription.encodeNatAppend 0 suffix := by
  rfl

theorem encodeOptionalCodeSymbolAppend_some
    (symbol : MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    encodeOptionalCodeSymbolAppend (some symbol) suffix =
      MachineDescription.encodeNatAppend
        (codeSymbolTag symbol + 1) suffix := by
  rfl

def decodeOptionalCodeSymbol
    (tokens : Word MachineCodeSymbol) :
    Option (Option MachineCodeSymbol × Word MachineCodeSymbol) :=
  match MachineDescription.decodeNat tokens with
  | none => none
  | some (tag, rest) =>
      match decodeOptionalCodeSymbolTag tag with
      | none => none
      | some cell => some (cell, rest)

theorem decodeOptionalCodeSymbol_encodeOptionalCodeSymbolAppend
    (cell : Option MachineCodeSymbol)
    (suffix : Word MachineCodeSymbol) :
    decodeOptionalCodeSymbol
        (encodeOptionalCodeSymbolAppend cell suffix) =
      some (cell, suffix) := by
  simp [decodeOptionalCodeSymbol, encodeOptionalCodeSymbolAppend,
    MachineDescription.decodeNat_encodeNatAppend,
    decodeOptionalCodeSymbolTag_optionalCodeSymbolTag]

def encodeOptionalCodeSymbolsPayloadAppend :
    List (Option MachineCodeSymbol) ->
      Word MachineCodeSymbol -> Word MachineCodeSymbol
  | [], suffix => suffix
  | cell :: rest, suffix =>
      encodeOptionalCodeSymbolAppend cell
        (encodeOptionalCodeSymbolsPayloadAppend rest suffix)

def decodeOptionalCodeSymbolsPayload :
    Nat -> Word MachineCodeSymbol ->
      Option (List (Option MachineCodeSymbol) × Word MachineCodeSymbol)
  | 0, tokens => some ([], tokens)
  | n + 1, tokens =>
      match decodeOptionalCodeSymbol tokens with
      | none => none
      | some (cell, rest) =>
          match decodeOptionalCodeSymbolsPayload n rest with
          | none => none
          | some (cells, suffix) => some (cell :: cells, suffix)

theorem decodeOptionalCodeSymbolsPayload_encode
    (cells : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    decodeOptionalCodeSymbolsPayload cells.length
        (encodeOptionalCodeSymbolsPayloadAppend cells suffix) =
      some (cells, suffix) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      simp [encodeOptionalCodeSymbolsPayloadAppend,
        decodeOptionalCodeSymbolsPayload,
        decodeOptionalCodeSymbol_encodeOptionalCodeSymbolAppend, ih]

def encodeOptionalCodeSymbolsAppend
    (cells : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineDescription.encodeNatAppend cells.length
    (encodeOptionalCodeSymbolsPayloadAppend cells suffix)

theorem encodeOptionalCodeSymbolsAppend_nil
    (suffix : Word MachineCodeSymbol) :
    encodeOptionalCodeSymbolsAppend [] suffix =
      MachineDescription.encodeNatAppend 0 suffix := by
  rfl

theorem encodeOptionalCodeSymbolsAppend_cons
    (cell : Option MachineCodeSymbol)
    (cells : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    encodeOptionalCodeSymbolsAppend (cell :: cells) suffix =
      MachineDescription.encodeNatAppend (cells.length + 1)
        (encodeOptionalCodeSymbolAppend cell
          (encodeOptionalCodeSymbolsPayloadAppend cells suffix)) := by
  rfl

def decodeOptionalCodeSymbols
    (tokens : Word MachineCodeSymbol) :
    Option
      (List (Option MachineCodeSymbol) × Word MachineCodeSymbol) :=
  match MachineDescription.decodeNat tokens with
  | none => none
  | some (count, rest) =>
      decodeOptionalCodeSymbolsPayload count rest

theorem decodeOptionalCodeSymbols_encodeOptionalCodeSymbolsAppend
    (cells : List (Option MachineCodeSymbol))
    (suffix : Word MachineCodeSymbol) :
    decodeOptionalCodeSymbols
        (encodeOptionalCodeSymbolsAppend cells suffix) =
      some (cells, suffix) := by
  simp [decodeOptionalCodeSymbols, encodeOptionalCodeSymbolsAppend,
    MachineDescription.decodeNat_encodeNatAppend,
    decodeOptionalCodeSymbolsPayload_encode]

/-- Protected exact-fuel work layout for a finite-state code-symbol machine. -/
structure Layout (stateCount : Nat) where
  fuel : Nat
  state : Fin stateCount
  left : List (Option MachineCodeSymbol)
  head : Option MachineCodeSymbol
  right : List (Option MachineCodeSymbol)

namespace Layout

def tape {stateCount : Nat} (L : Layout stateCount) :
    Tape MachineCodeSymbol where
  left := L.left
  head := L.head
  right := L.right

def config {stateCount : Nat} (L : Layout stateCount) :
    TuringMachine.Configuration MachineCodeSymbol (Fin stateCount) where
  state := L.state
  tape := L.tape

def ofConfig {stateCount : Nat}
    (fuel : Nat)
    (c : TuringMachine.Configuration MachineCodeSymbol (Fin stateCount)) :
    Layout stateCount where
  fuel := fuel
  state := c.state
  left := c.tape.left
  head := c.tape.head
  right := c.tape.right

theorem config_ofConfig {stateCount : Nat}
    (fuel : Nat)
    (c : TuringMachine.Configuration MachineCodeSymbol (Fin stateCount)) :
    (ofConfig fuel c).config = c := by
  cases c
  rfl

def initial {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    Layout stateCount :=
  ofConfig fuel (TuringMachine.initial M input)

theorem config_initial {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    (initial M input fuel).config =
      TuringMachine.initial M input := by
  exact config_ofConfig fuel (TuringMachine.initial M input)

theorem initial_empty_eq {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) :
    initial M ([] : Word MachineCodeSymbol) fuel =
      { fuel := fuel
        state := M.start
        left := []
        head := none
        right := [] } := by
  rfl

theorem initial_cons_eq {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (fuel : Nat) :
    initial M (symbol :: rest) fuel =
      { fuel := fuel
        state := M.start
        left := []
        head := some symbol
        right := rest.map some } := by
  rfl

theorem initial_fuel {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    (initial M input fuel).fuel = fuel := by
  cases input <;> rfl

theorem initial_state {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    (initial M input fuel).state = M.start := by
  cases input <;> rfl

theorem initial_left {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    (initial M input fuel).left = [] := by
  cases input <;> rfl

theorem initial_empty_head {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) :
    (initial M ([] : Word MachineCodeSymbol) fuel).head = none := by
  rfl

theorem initial_cons_head {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (fuel : Nat) :
    (initial M (symbol :: rest) fuel).head = some symbol := by
  rfl

theorem initial_empty_right {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) :
    (initial M ([] : Word MachineCodeSymbol) fuel).right = [] := by
  rfl

theorem initial_cons_right {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (fuel : Nat) :
    (initial M (symbol :: rest) fuel).right = rest.map some := by
  rfl

def decodeState (stateCount state : Nat) :
    Option (Fin stateCount) :=
  if h : state < stateCount then
    some ⟨state, h⟩
  else
    none

theorem decodeState_val {stateCount : Nat}
    (state : Fin stateCount) :
    decodeState stateCount state.val = some state := by
  cases state with
  | mk val isLt =>
      simp [decodeState, isLt]

def encodeAppend {stateCount : Nat}
    (L : Layout stateCount)
    (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    MachineDescription.encodeNatAppend L.fuel
      (MachineDescription.encodeNatAppend L.state.val
        (encodeOptionalCodeSymbolsAppend L.left
          (encodeOptionalCodeSymbolAppend L.head
            (encodeOptionalCodeSymbolsAppend L.right suffix))))

def encode {stateCount : Nat} (L : Layout stateCount) :
    Word MachineCodeSymbol :=
  encodeAppend L []

theorem encode_initial_empty {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) :
    encode (initial M ([] : Word MachineCodeSymbol) fuel) =
      MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend fuel
          (MachineDescription.encodeNatAppend M.start.val
            (encodeOptionalCodeSymbolsAppend []
              (encodeOptionalCodeSymbolAppend none
                (encodeOptionalCodeSymbolsAppend [] [])))) := by
  rfl

theorem encode_initial_empty_expanded {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (fuel : Nat) :
    encode (initial M ([] : Word MachineCodeSymbol) fuel) =
      MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend fuel
          (MachineDescription.encodeNatAppend M.start.val
            (MachineDescription.encodeNatAppend 0
              (MachineDescription.encodeNatAppend 0
                (MachineDescription.encodeNatAppend 0 [])))) := by
  rfl

theorem encode_initial_cons {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (fuel : Nat) :
    encode (initial M (symbol :: rest) fuel) =
      MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend fuel
          (MachineDescription.encodeNatAppend M.start.val
            (encodeOptionalCodeSymbolsAppend []
              (encodeOptionalCodeSymbolAppend (some symbol)
                (encodeOptionalCodeSymbolsAppend (rest.map some) [])))) := by
  rfl

theorem encode_initial_cons_expanded {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (symbol : MachineCodeSymbol)
    (rest : Word MachineCodeSymbol) (fuel : Nat) :
    encode (initial M (symbol :: rest) fuel) =
      MachineCodeSymbol.header ::
        MachineDescription.encodeNatAppend fuel
          (MachineDescription.encodeNatAppend M.start.val
            (MachineDescription.encodeNatAppend 0
              (MachineDescription.encodeNatAppend
                (codeSymbolTag symbol + 1)
                (encodeOptionalCodeSymbolsAppend (rest.map some) [])))) := by
  rfl

def decode (stateCount : Nat)
    (tokens : Word MachineCodeSymbol) :
    Option (Layout stateCount × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.header :: rest =>
      match MachineDescription.decodeNat rest with
      | none => none
      | some (fuel, rest) =>
          match MachineDescription.decodeNat rest with
          | none => none
          | some (stateNat, rest) =>
              match decodeState stateCount stateNat with
              | none => none
              | some state =>
                  match decodeOptionalCodeSymbols rest with
                  | none => none
                  | some (left, rest) =>
                      match decodeOptionalCodeSymbol rest with
                      | none => none
                      | some (head, rest) =>
                          match decodeOptionalCodeSymbols rest with
                          | none => none
                          | some (right, suffix) =>
                              some
                                ({ fuel := fuel
                                   state := state
                                   left := left
                                   head := head
                                   right := right },
                                  suffix)
  | _ => none

theorem decode_encodeAppend {stateCount : Nat}
    (L : Layout stateCount)
    (suffix : Word MachineCodeSymbol) :
    decode stateCount (encodeAppend L suffix) =
      some (L, suffix) := by
  cases L with
  | mk fuel state left head right =>
      simp [decode, encodeAppend,
        MachineDescription.decodeNat_encodeNatAppend,
        decodeState_val,
        decodeOptionalCodeSymbols_encodeOptionalCodeSymbolsAppend,
        decodeOptionalCodeSymbol_encodeOptionalCodeSymbolAppend]

theorem decode_encode {stateCount : Nat}
    (L : Layout stateCount) :
    decode stateCount (encode L) = some (L, []) := by
  exact decode_encodeAppend L []

def stageCodeToInitialLayoutCode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match MachineDescription.decodeNat tokens with
  | none => none
  | some (fuel, input) => some (encode (initial M input fuel))

theorem stageCodeToInitialLayoutCode_stageCode {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    stageCodeToInitialLayoutCode M
        (MachineDescription.encodeNatAppend fuel input) =
      some (encode (initial M input fuel)) := by
  simp [stageCodeToInitialLayoutCode,
    MachineDescription.decodeNat_encodeNatAppend]

def accepts {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) : Prop :=
  TuringMachine.HaltsFromIn M L.fuel L.config

theorem accepts_iff_haltsFromIn {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) :
    accepts M L <->
      TuringMachine.HaltsFromIn M L.fuel L.config := by
  rfl

theorem accepts_zero_iff {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) :
    accepts M { L with fuel := 0 } <->
      TuringMachine.Halted M ({ L with fuel := 0 }).config := by
  exact TuringMachine.haltsFromIn_zero_iff

def step {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount) : Option (Layout stateCount) :=
  match L.fuel with
  | 0 => none
  | fuel + 1 =>
      match M.transition L.state (Tape.read L.tape) with
      | none => none
      | some (write, dir, nextState) =>
          some
            (ofConfig fuel
              { state := nextState
                tape := Tape.move dir (Tape.write write L.tape) })

theorem step_eq_none_of_fuel_zero {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (L : Layout stateCount)
    (hfuel : L.fuel = 0) :
    step M L = none := by
  cases L with
  | mk layoutFuel state left head right =>
      cases hfuel
      rfl

theorem step_of_transition_eq_some {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {L : Layout stateCount} {fuel : Nat}
    {write : Option MachineCodeSymbol} {dir : Direction}
    {nextState : Fin stateCount}
    (hfuel : L.fuel = fuel + 1)
    (htransition :
      M.transition L.state (Tape.read L.tape) =
        some (write, dir, nextState)) :
    step M L =
      some
        (ofConfig fuel
          { state := nextState
            tape := Tape.move dir (Tape.write write L.tape) }) := by
  cases L with
  | mk layoutFuel state left head right =>
      cases hfuel
      have htransition' :
          M.transition state
              (Tape.read
                ({ left := left, head := head, right := right } :
                  Tape MachineCodeSymbol)) =
            some (write, dir, nextState) := by
        simpa [tape] using htransition
      simp [step, tape]
      rw [htransition']

theorem step_eq_none_of_transition_eq_none {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {L : Layout stateCount} {fuel : Nat}
    (hfuel : L.fuel = fuel + 1)
    (htransition :
      M.transition L.state (Tape.read L.tape) = none) :
    step M L = none := by
  cases L with
  | mk layoutFuel state left head right =>
      cases hfuel
      have htransition' :
          M.transition state
              (Tape.read
                ({ left := left, head := head, right := right } :
                  Tape MachineCodeSymbol)) = none := by
        simpa [tape] using htransition
      simp [step, tape]
      rw [htransition']

theorem step_eq_some_iff {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {L L' : Layout stateCount} :
    step M L = some L' <->
      exists fuel : Nat,
      exists write : Option MachineCodeSymbol,
      exists dir : Direction,
      exists nextState : Fin stateCount,
        L.fuel = fuel + 1 /\
          M.transition L.state (Tape.read L.tape) =
            some (write, dir, nextState) /\
          L' =
            ofConfig fuel
              { state := nextState
                tape := Tape.move dir (Tape.write write L.tape) } := by
  constructor
  · intro hstep
    cases L with
    | mk layoutFuel state left head right =>
        cases layoutFuel with
        | zero =>
            simp [step] at hstep
        | succ fuel =>
            cases htransition :
                M.transition state
                  (Tape.read
                    ({ left := left, head := head, right := right } :
                      Tape MachineCodeSymbol)) with
            | none =>
                simp [step, tape, htransition] at hstep
            | some action =>
                rcases action with ⟨write, dir, nextState⟩
                simp [step, tape, htransition] at hstep
                subst L'
                exact
                  ⟨fuel, write, dir, nextState, rfl,
                    by simpa [tape] using htransition, rfl⟩
  · intro h
    rcases h with
      ⟨fuel, write, dir, nextState, hfuel, htransition, hL'⟩
    subst L'
    exact
      step_of_transition_eq_some
        (M := M) (L := L) hfuel htransition

theorem step_fuel_eq_of_eq_some {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    {L L' : Layout stateCount} {fuel : Nat}
    (hfuel : L.fuel = fuel + 1)
    (hstep : step M L = some L') :
    L'.fuel = fuel := by
  rcases (step_eq_some_iff.mp hstep) with
    ⟨fuel', write, dir, nextState, hfuel', _htransition, hL'⟩
  have hfuelEq : fuel' = fuel := by
    exact Nat.succ.inj (hfuel'.symm.trans hfuel)
  subst fuel'
  subst L'
  rfl

theorem accepts_succ_transition_iff {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (L : Layout stateCount) (fuel : Nat)
    (hfuel : L.fuel = fuel + 1) :
    accepts M L <->
      exists write : Option MachineCodeSymbol,
      exists dir : Direction,
      exists nextState : Fin stateCount,
        M.transition L.state (Tape.read L.tape) =
          some (write, dir, nextState) /\
          accepts M
            (ofConfig fuel
              { state := nextState
                tape := Tape.move dir (Tape.write write L.tape) }) := by
  cases L with
  | mk layoutFuel state left head right =>
      cases hfuel
      simpa [accepts, config, tape, config_ofConfig] using
        (TuringMachine.haltsFromIn_succ_transition_iff
          (M := M) (n := fuel)
          (c :=
            { state := state
              tape := { left := left, head := head, right := right } }))

theorem accepts_succ_iff_of_transition_eq_some {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (L : Layout stateCount) (fuel : Nat)
    (hfuel : L.fuel = fuel + 1)
    {write : Option MachineCodeSymbol} {dir : Direction}
    {nextState : Fin stateCount}
    (htransition :
      M.transition L.state (Tape.read L.tape) =
        some (write, dir, nextState)) :
    accepts M L <->
      accepts M
        (ofConfig fuel
          { state := nextState
            tape := Tape.move dir (Tape.write write L.tape) }) := by
  cases L with
  | mk layoutFuel state left head right =>
      cases hfuel
      simpa [accepts, config, tape, config_ofConfig] using
        (TuringMachine.haltsFromIn_succ_iff_of_transition_eq_some
          (M := M) (n := fuel)
          (c :=
            { state := state
              tape := { left := left, head := head, right := right } })
          htransition)

theorem accepts_succ_iff_false_of_transition_eq_none {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (L : Layout stateCount) (fuel : Nat)
    (hfuel : L.fuel = fuel + 1)
    (htransition :
      M.transition L.state (Tape.read L.tape) = none) :
    accepts M L <-> False := by
  cases L with
  | mk layoutFuel state left head right =>
      cases hfuel
      simpa [accepts, config, tape] using
        (TuringMachine.haltsFromIn_succ_iff_false_of_transition_eq_none
          (M := M) (n := fuel)
          (c :=
            { state := state
              tape := { left := left, head := head, right := right } })
          htransition)

theorem accepts_succ_iff_step {stateCount : Nat}
    {M : TuringMachine MachineCodeSymbol (Fin stateCount)}
    (L : Layout stateCount) (fuel : Nat)
    (hfuel : L.fuel = fuel + 1) :
    accepts M L <->
      exists L' : Layout stateCount,
        step M L = some L' /\ accepts M L' := by
  constructor
  · intro haccepts
    rcases
        (accepts_succ_transition_iff
          (M := M) L fuel hfuel).mp haccepts with
      ⟨write, dir, nextState, htransition, htail⟩
    refine
      ⟨ofConfig fuel
        { state := nextState
          tape := Tape.move dir (Tape.write write L.tape) },
        ?_, htail⟩
    exact step_of_transition_eq_some
      (M := M) (L := L) hfuel htransition
  · intro h
    rcases h with ⟨L', hstep, htail⟩
    cases L with
    | mk layoutFuel state left head right =>
        cases hfuel
        cases htransition :
            M.transition state
              (Tape.read
                ({ left := left, head := head, right := right } :
                  Tape MachineCodeSymbol)) with
        | none =>
            simp [step, tape, htransition] at hstep
        | some action =>
            rcases action with ⟨write, dir, nextState⟩
            simp [step, tape, htransition] at hstep
            cases hstep
            exact
              (accepts_succ_iff_of_transition_eq_some
                (M := M)
                { fuel := fuel + 1
                  state := state
                  left := left
                  head := head
                  right := right }
                fuel rfl htransition).mpr htail

theorem accepts_initial_iff_haltsOnInputIn {stateCount : Nat}
    (M : TuringMachine MachineCodeSymbol (Fin stateCount))
    (input : Word MachineCodeSymbol) (fuel : Nat) :
    accepts M (initial M input fuel) <->
      TuringMachine.HaltsOnInputIn M fuel input := by
  rfl

end Layout

end ExactFuel
end FiniteRecognizer

end Computability
end FoC
