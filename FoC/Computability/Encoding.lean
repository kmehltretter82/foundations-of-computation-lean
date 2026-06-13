import FoC.Computability.TuringMachine

set_option doc.verso true

/-!
# Machine descriptions and interpretation

This module starts the concrete encoding/interpreter layer needed for the
remaining Chapter 5 theorems.  It introduces a finite token alphabet for
binary-tape machine descriptions, a decoder for that syntax, a well-formedness
predicate for decoded transition tables, and an interpreter semantics that can
also be compiled into the existing one-tape
{name}`FoC.Computability.TuringMachine` model.

The descriptions here are intentionally first-order data: they are finite
lists of transition records, not arbitrary Lean functions.  This keeps later
compiler and universal-machine theorems tied to concrete syntax.

## Book coordinates

Used by:
- Chapter 5, Sections 5.2 and 5.3: concrete machine encodings and universal
  interpretation infrastructure.
-/

namespace FoC
namespace Computability

open Foundation
open Languages

/-!
# Finite description alphabet

Natural numbers are encoded in unary by a sequence of {lit}`tick` tokens
terminated by {lit}`done`.  The remaining tokens identify headers,
transition records, cells, and movement directions.
-/

inductive MachineCodeSymbol where
  | header : MachineCodeSymbol
  | transition : MachineCodeSymbol
  | tick : MachineCodeSymbol
  | done : MachineCodeSymbol
  | blank : MachineCodeSymbol
  | zero : MachineCodeSymbol
  | one : MachineCodeSymbol
  | moveLeft : MachineCodeSymbol
  | moveRight : MachineCodeSymbol
deriving DecidableEq

namespace MachineCodeSymbol

def finite : FiniteType MachineCodeSymbol where
  elems :=
    [ header, transition, tick, done, blank, zero, one, moveLeft, moveRight ]
  complete := by
    intro symbol
    cases symbol <;> simp

end MachineCodeSymbol

def finFinite (n : Nat) : FiniteType (Fin n) where
  elems := List.finRange n
  complete := List.mem_finRange

/-!
# Transition and machine descriptions
-/

structure TransitionDescription where
  source : Nat
  read : Option Bool
  write : Option Bool
  move : Direction
  target : Nat
deriving DecidableEq

structure MachineDescription where
  stateCount : Nat
  start : Nat
  halt : Nat
  transitions : List TransitionDescription
deriving DecidableEq

namespace TransitionDescription

def WellFormed (stateCount : Nat) (t : TransitionDescription) : Prop :=
  t.source < stateCount ∧ t.target < stateCount

def SameKey (t u : TransitionDescription) : Prop :=
  t.source = u.source ∧ t.read = u.read

def SameAction (t u : TransitionDescription) : Prop :=
  t.write = u.write ∧ t.move = u.move ∧ t.target = u.target

end TransitionDescription

namespace MachineDescription

def Deterministic (D : MachineDescription) : Prop :=
  forall t u : TransitionDescription,
    t ∈ D.transitions -> u ∈ D.transitions ->
      TransitionDescription.SameKey t u ->
        TransitionDescription.SameAction t u

def WellFormed (D : MachineDescription) : Prop :=
  0 < D.stateCount ∧
    D.start < D.stateCount ∧
    D.halt < D.stateCount ∧
    (forall t : TransitionDescription,
      t ∈ D.transitions ->
        TransitionDescription.WellFormed D.stateCount t) ∧
    D.Deterministic

def Matches (source : Nat) (read : Option Bool)
    (t : TransitionDescription) : Bool :=
  t.source == source && t.read == read

def lookupTransition (D : MachineDescription)
    (source : Nat) (read : Option Bool) :
    Option TransitionDescription :=
  D.transitions.find? (Matches source read)

structure Configuration where
  state : Nat
  tape : Tape Bool
deriving DecidableEq

def initial (D : MachineDescription) (w : Word Bool) :
    Configuration where
  state := D.start
  tape := Tape.input w

def stepConfig (D : MachineDescription)
    (c : Configuration) : Option Configuration :=
  match D.lookupTransition c.state (Tape.read c.tape) with
  | none => none
  | some t =>
      some
        { state := t.target
          tape := Tape.move t.move (Tape.write t.write c.tape) }

def runConfig (D : MachineDescription) :
    Nat -> Configuration -> Configuration
  | 0, c => c
  | n + 1, c =>
      match D.stepConfig c with
      | none => c
      | some next => runConfig D n next

def HaltsIn (D : MachineDescription) (n : Nat) (w : Word Bool) : Prop :=
  (D.runConfig n (D.initial w)).state = D.halt

def HaltsOnInput (D : MachineDescription) (w : Word Bool) : Prop :=
  exists n : Nat, D.HaltsIn n w

def stateOfNat (D : MachineDescription) (n : Nat) :
    Fin (D.stateCount + 1) :=
  if h : n < D.stateCount + 1 then
    ⟨n, h⟩
  else
    ⟨D.stateCount, Nat.lt_succ_self D.stateCount⟩

theorem stateOfNat_val_of_lt {D : MachineDescription} {n : Nat}
    (h : n < D.stateCount + 1) :
    (D.stateOfNat n).val = n := by
  simp [stateOfNat, h]

def toTMConfig (D : MachineDescription) (c : Configuration) :
    TuringMachine.Configuration Bool (Fin (D.stateCount + 1)) where
  state := D.stateOfNat c.state
  tape := c.tape

def toTuringMachine (D : MachineDescription) :
    TuringMachine Bool (Fin (D.stateCount + 1)) where
  start := D.stateOfNat D.start
  halt := D.stateOfNat D.halt
  transition := fun q cell =>
    match D.lookupTransition q.val cell with
    | none => none
    | some t => some (t.write, t.move, D.stateOfNat t.target)
  statesFinite := finFinite (D.stateCount + 1)

theorem toTuringMachine_transition_of_lookup
    {D : MachineDescription} {source : Nat} {read : Option Bool}
    {t : TransitionDescription}
    (hsource : source < D.stateCount + 1)
    (hlookup : D.lookupTransition source read = some t) :
    (D.toTuringMachine).transition (D.stateOfNat source) read =
      some (t.write, t.move, D.stateOfNat t.target) := by
  simp [toTuringMachine, stateOfNat_val_of_lt hsource, hlookup]

theorem toTuringMachine_step_of_stepConfig
    {D : MachineDescription} {c d : Configuration}
    (hsource : c.state < D.stateCount + 1)
    (hstep : D.stepConfig c = some d) :
    TuringMachine.Step D.toTuringMachine
      (D.toTMConfig c) (D.toTMConfig d) := by
  unfold stepConfig at hstep
  cases hlookup : D.lookupTransition c.state (Tape.read c.tape) with
  | none =>
      rw [hlookup] at hstep
      cases hstep
  | some t =>
      rw [hlookup] at hstep
      cases hstep
      exact TuringMachine.Step.mk
        (toTuringMachine_transition_of_lookup
          (D := D) (source := c.state)
          (read := Tape.read c.tape) hsource hlookup)

/-!
# Encoding and decoding
-/

def encodeNat : Nat -> Word MachineCodeSymbol
  | 0 => [MachineCodeSymbol.done]
  | n + 1 => MachineCodeSymbol.tick :: encodeNat n

def decodeNat : Word MachineCodeSymbol ->
    Option (Nat × Word MachineCodeSymbol)
  | MachineCodeSymbol.done :: rest => some (0, rest)
  | MachineCodeSymbol.tick :: rest =>
      match decodeNat rest with
      | none => none
      | some (n, rest') => some (n + 1, rest')
  | _ => none

theorem decodeNat_encodeNat_append
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    decodeNat (List.append (encodeNat n) suffix) = some (n, suffix) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (match decodeNat (List.append (encodeNat n) suffix) with
        | none => none
        | some (n, rest') => some (n + 1, rest')) =
          some (n + 1, suffix)
      rw [ih]

def encodeCell : Option Bool -> Word MachineCodeSymbol
  | none => [MachineCodeSymbol.blank]
  | some false => [MachineCodeSymbol.zero]
  | some true => [MachineCodeSymbol.one]

def decodeCell : Word MachineCodeSymbol ->
    Option (Option Bool × Word MachineCodeSymbol)
  | MachineCodeSymbol.blank :: rest => some (none, rest)
  | MachineCodeSymbol.zero :: rest => some (some false, rest)
  | MachineCodeSymbol.one :: rest => some (some true, rest)
  | _ => none

theorem decodeCell_encodeCell_append
    (cell : Option Bool) (suffix : Word MachineCodeSymbol) :
    decodeCell (List.append (encodeCell cell) suffix) =
      some (cell, suffix) := by
  cases cell with
  | none => rfl
  | some b =>
      cases b <;> rfl

def encodeDirection : Direction -> Word MachineCodeSymbol
  | Direction.left => [MachineCodeSymbol.moveLeft]
  | Direction.right => [MachineCodeSymbol.moveRight]

def decodeDirection : Word MachineCodeSymbol ->
    Option (Direction × Word MachineCodeSymbol)
  | MachineCodeSymbol.moveLeft :: rest => some (Direction.left, rest)
  | MachineCodeSymbol.moveRight :: rest => some (Direction.right, rest)
  | _ => none

theorem decodeDirection_encodeDirection_append
    (dir : Direction) (suffix : Word MachineCodeSymbol) :
    decodeDirection (List.append (encodeDirection dir) suffix) =
      some (dir, suffix) := by
  cases dir <;> rfl

def encodeNatAppend (n : Nat) (suffix : Word MachineCodeSymbol) :
    Word MachineCodeSymbol :=
  List.append (encodeNat n) suffix

def encodeCellAppend (cell : Option Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (encodeCell cell) suffix

def encodeDirectionAppend (dir : Direction)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  List.append (encodeDirection dir) suffix

theorem decodeNat_encodeNatAppend
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    decodeNat (encodeNatAppend n suffix) = some (n, suffix) :=
  decodeNat_encodeNat_append n suffix

theorem decodeNat_eq_some_encodeNatAppend
    {tokens : Word MachineCodeSymbol} {n : Nat}
    {suffix : Word MachineCodeSymbol}
    (h : decodeNat tokens = some (n, suffix)) :
    tokens = encodeNatAppend n suffix := by
  induction tokens generalizing n suffix with
  | nil =>
      cases h
  | cons symbol rest ih =>
      cases symbol with
      | header => cases h
      | transition => cases h
      | tick =>
          simp [decodeNat] at h
          cases hrest : decodeNat rest with
          | none =>
              simp [hrest] at h
          | some parsed =>
              cases parsed with
              | mk parsedN parsedSuffix =>
                  simp [hrest] at h
                  have hcanonical :
                      rest = encodeNatAppend parsedN parsedSuffix :=
                    ih hrest
                  cases h
                  subst n
                  subst suffix
                  simp [encodeNatAppend, encodeNat, hcanonical]
      | done =>
          simp [decodeNat] at h
          cases h
          subst n
          subst suffix
          rfl
      | blank => cases h
      | zero => cases h
      | one => cases h
      | moveLeft => cases h
      | moveRight => cases h

theorem decodeCell_encodeCellAppend
    (cell : Option Bool) (suffix : Word MachineCodeSymbol) :
    decodeCell (encodeCellAppend cell suffix) = some (cell, suffix) :=
  decodeCell_encodeCell_append cell suffix

theorem decodeCell_eq_some_encodeCellAppend
    {tokens : Word MachineCodeSymbol} {cell : Option Bool}
    {suffix : Word MachineCodeSymbol}
    (h : decodeCell tokens = some (cell, suffix)) :
    tokens = encodeCellAppend cell suffix := by
  cases tokens with
  | nil =>
      cases h
  | cons symbol rest =>
      cases symbol <;> simp [decodeCell] at h
      · cases h
        subst cell
        subst suffix
        rfl
      · cases h
        subst cell
        subst suffix
        rfl
      · cases h
        subst cell
        subst suffix
        rfl

theorem decodeDirection_encodeDirectionAppend
    (dir : Direction) (suffix : Word MachineCodeSymbol) :
    decodeDirection (encodeDirectionAppend dir suffix) =
      some (dir, suffix) :=
  decodeDirection_encodeDirection_append dir suffix

theorem decodeDirection_eq_some_encodeDirectionAppend
    {tokens : Word MachineCodeSymbol} {dir : Direction}
    {suffix : Word MachineCodeSymbol}
    (h : decodeDirection tokens = some (dir, suffix)) :
    tokens = encodeDirectionAppend dir suffix := by
  cases tokens with
  | nil =>
      cases h
  | cons symbol rest =>
      cases symbol <;> simp [decodeDirection] at h
      · cases h
        subst dir
        subst suffix
        rfl
      · cases h
        subst dir
        subst suffix
        rfl

def encodeTransitionAppend (t : TransitionDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.transition ::
    encodeNatAppend t.source
      (encodeCellAppend t.read
        (encodeCellAppend t.write
          (encodeDirectionAppend t.move
            (encodeNatAppend t.target suffix))))

def encodeTransition (t : TransitionDescription) :
    Word MachineCodeSymbol :=
  encodeTransitionAppend t []

def decodeTransition (tokens : Word MachineCodeSymbol) :
    Option (TransitionDescription × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.transition :: rest =>
      match decodeNat rest with
      | none => none
      | some (source, rest) =>
          match decodeCell rest with
          | none => none
          | some (read, rest) =>
              match decodeCell rest with
              | none => none
              | some (write, rest) =>
                  match decodeDirection rest with
                  | none => none
                  | some (move, rest) =>
                      match decodeNat rest with
                      | none => none
                      | some (target, rest) =>
                          some
                            ({ source := source
                               read := read
                               write := write
                               move := move
                               target := target }, rest)
  | _ => none

theorem decodeTransition_encodeTransition_append
    (t : TransitionDescription) (suffix : Word MachineCodeSymbol) :
    decodeTransition (encodeTransitionAppend t suffix) =
      some (t, suffix) := by
  cases t
  simp [encodeTransitionAppend, decodeTransition,
    decodeNat_encodeNatAppend,
    decodeCell_encodeCellAppend,
    decodeDirection_encodeDirectionAppend]

theorem decodeTransition_encodeTransition :
    decodeTransition (encodeTransition t) = some (t, []) := by
  exact decodeTransition_encodeTransition_append t []

theorem decodeTransition_eq_some_encodeTransitionAppend
    {tokens : Word MachineCodeSymbol} {t : TransitionDescription}
    {suffix : Word MachineCodeSymbol}
    (h : decodeTransition tokens = some (t, suffix)) :
    tokens = encodeTransitionAppend t suffix := by
  cases tokens with
  | nil =>
      cases h
  | cons symbol rest =>
      cases symbol with
      | header => cases h
      | transition =>
          simp [decodeTransition] at h
          cases hsource : decodeNat rest with
          | none =>
              simp [hsource] at h
          | some parsedSource =>
              cases parsedSource with
              | mk source restAfterSource =>
                  simp [hsource] at h
                  cases hread : decodeCell restAfterSource with
                  | none =>
                      simp [hread] at h
                  | some parsedRead =>
                      cases parsedRead with
                      | mk read restAfterRead =>
                          simp [hread] at h
                          cases hwrite : decodeCell restAfterRead with
                          | none =>
                              simp [hwrite] at h
                          | some parsedWrite =>
                              cases parsedWrite with
                              | mk write restAfterWrite =>
                                  simp [hwrite] at h
                                  cases hmove :
                                      decodeDirection restAfterWrite with
                                  | none =>
                                      simp [hmove] at h
                                  | some parsedMove =>
                                      cases parsedMove with
                                      | mk move restAfterMove =>
                                          simp [hmove] at h
                                          cases htarget :
                                              decodeNat restAfterMove with
                                          | none =>
                                              simp [htarget] at h
                                          | some parsedTarget =>
                                              cases parsedTarget with
                                              | mk target parsedSuffix =>
                                                  simp [htarget] at h
                                                  cases h
                                                  subst t
                                                  subst suffix
                                                  have hsourceTokens :
                                                      rest =
                                                        encodeNatAppend source
                                                          restAfterSource :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      hsource
                                                  have hreadTokens :
                                                      restAfterSource =
                                                        encodeCellAppend read
                                                          restAfterRead :=
                                                    decodeCell_eq_some_encodeCellAppend
                                                      hread
                                                  have hwriteTokens :
                                                      restAfterRead =
                                                        encodeCellAppend write
                                                          restAfterWrite :=
                                                    decodeCell_eq_some_encodeCellAppend
                                                      hwrite
                                                  have hmoveTokens :
                                                      restAfterWrite =
                                                        encodeDirectionAppend
                                                          move restAfterMove :=
                                                    decodeDirection_eq_some_encodeDirectionAppend
                                                      hmove
                                                  have htargetTokens :
                                                      restAfterMove =
                                                        encodeNatAppend target
                                                          parsedSuffix :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      htarget
                                                  simp [encodeTransitionAppend,
                                                    hsourceTokens,
                                                    hreadTokens,
                                                    hwriteTokens,
                                                    hmoveTokens,
                                                    htargetTokens]
      | tick => cases h
      | done => cases h
      | blank => cases h
      | zero => cases h
      | one => cases h
      | moveLeft => cases h
      | moveRight => cases h

def encodeTransitionsAppend : List TransitionDescription ->
    Word MachineCodeSymbol -> Word MachineCodeSymbol
  | [], suffix => suffix
  | t :: rest, suffix =>
      encodeTransitionAppend t (encodeTransitionsAppend rest suffix)

def encodeTransitions (transitions : List TransitionDescription) :
    Word MachineCodeSymbol :=
  encodeTransitionsAppend transitions []

theorem encodeTransitionsAppend_append
    (transitions : List TransitionDescription)
    (suffix tail : Word MachineCodeSymbol) :
    List.append (encodeTransitionsAppend transitions suffix) tail =
      encodeTransitionsAppend transitions (List.append suffix tail) := by
  induction transitions with
  | nil =>
      rfl
  | cons t rest ih =>
      simpa [encodeTransitionsAppend, encodeTransitionAppend,
        encodeNatAppend, encodeCellAppend, encodeDirectionAppend,
        List.append_assoc] using ih

def decodeTransitions : Nat -> Word MachineCodeSymbol ->
    Option (List TransitionDescription × Word MachineCodeSymbol)
  | 0, tokens => some ([], tokens)
  | n + 1, tokens =>
      match decodeTransition tokens with
      | none => none
      | some (t, rest) =>
          match decodeTransitions n rest with
          | none => none
          | some (ts, rest') => some (t :: ts, rest')

theorem decodeTransitions_encodeTransitions_append
    (transitions : List TransitionDescription)
    (suffix : Word MachineCodeSymbol) :
    decodeTransitions transitions.length
      (encodeTransitionsAppend transitions suffix) =
        some (transitions, suffix) := by
  induction transitions with
  | nil =>
      rfl
  | cons t rest ih =>
      simp [encodeTransitionsAppend, decodeTransitions,
        decodeTransition_encodeTransition_append, ih]

theorem decodeTransitions_encodeTransitions
    (transitions : List TransitionDescription) :
    decodeTransitions transitions.length (encodeTransitions transitions) =
      some (transitions, []) :=
  decodeTransitions_encodeTransitions_append transitions []

theorem decodeTransitions_eq_some_encodeTransitionsAppend
    {count : Nat} {tokens : Word MachineCodeSymbol}
    {transitions : List TransitionDescription}
    {suffix : Word MachineCodeSymbol}
    (h : decodeTransitions count tokens = some (transitions, suffix)) :
    count = transitions.length ∧
      tokens = encodeTransitionsAppend transitions suffix := by
  induction count generalizing tokens transitions suffix with
  | zero =>
      simp [decodeTransitions] at h
      cases h
      subst transitions
      subst tokens
      constructor <;> rfl
  | succ count ih =>
      simp [decodeTransitions] at h
      cases htransition : decodeTransition tokens with
      | none =>
          simp [htransition] at h
      | some parsedTransition =>
          cases parsedTransition with
          | mk transition rest =>
              simp [htransition] at h
              cases htail : decodeTransitions count rest with
              | none =>
                  simp [htail] at h
              | some parsedTail =>
                  cases parsedTail with
                  | mk tail parsedSuffix =>
                      simp [htail] at h
                      cases h
                      subst transitions
                      subst suffix
                      have htokens :
                          tokens =
                            encodeTransitionAppend transition rest :=
                        decodeTransition_eq_some_encodeTransitionAppend
                          htransition
                      have hrest :
                          count = tail.length ∧
                            rest =
                              encodeTransitionsAppend tail parsedSuffix :=
                        ih htail
                      constructor
                      · simp [hrest.left]
                      · simp [encodeTransitionsAppend, htokens,
                          hrest.right]

def encodeDescriptionAppend (D : MachineDescription)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  MachineCodeSymbol.header ::
    encodeNatAppend D.stateCount
      (encodeNatAppend D.start
        (encodeNatAppend D.halt
          (encodeNatAppend D.transitions.length
            (encodeTransitionsAppend D.transitions suffix))))

def encodeDescription (D : MachineDescription) :
    Word MachineCodeSymbol :=
  encodeDescriptionAppend D []

theorem encodeDescriptionAppend_eq_encodeDescription_append
    (D : MachineDescription) (suffix : Word MachineCodeSymbol) :
    encodeDescriptionAppend D suffix =
      List.append (encodeDescription D) suffix := by
  cases D with
  | mk stateCount start halt transitions =>
      simp [encodeDescription, encodeDescriptionAppend, encodeNatAppend,
        List.append_assoc]
      have htrans :
          List.append (encodeTransitionsAppend transitions []) suffix =
            encodeTransitionsAppend transitions suffix := by
        simpa using encodeTransitionsAppend_append transitions [] suffix
      rw [← htrans]
      rfl

def decodeDescription (tokens : Word MachineCodeSymbol) :
    Option MachineDescription :=
  match tokens with
  | MachineCodeSymbol.header :: rest =>
      match decodeNat rest with
      | none => none
      | some (stateCount, rest) =>
          match decodeNat rest with
          | none => none
          | some (start, rest) =>
              match decodeNat rest with
              | none => none
              | some (halt, rest) =>
                  match decodeNat rest with
                  | none => none
                  | some (transitionCount, rest) =>
                      match decodeTransitions transitionCount rest with
                      | none => none
                      | some (transitions, []) =>
                          some
                            { stateCount := stateCount
                              start := start
                              halt := halt
                              transitions := transitions }
                      | some (_, _ :: _) => none
  | _ => none

def decodeDescriptionPrefix (tokens : Word MachineCodeSymbol) :
    Option (MachineDescription × Word MachineCodeSymbol) :=
  match tokens with
  | MachineCodeSymbol.header :: rest =>
      match decodeNat rest with
      | none => none
      | some (stateCount, rest) =>
          match decodeNat rest with
          | none => none
          | some (start, rest) =>
              match decodeNat rest with
              | none => none
              | some (halt, rest) =>
                  match decodeNat rest with
                  | none => none
                  | some (transitionCount, rest) =>
                      match decodeTransitions transitionCount rest with
                      | none => none
                      | some (transitions, suffix) =>
                          some
                            ({ stateCount := stateCount
                               start := start
                               halt := halt
                               transitions := transitions }, suffix)
  | _ => none

theorem decodeDescription_encodeDescription
    (D : MachineDescription) :
    decodeDescription (encodeDescription D) = some D := by
  cases D
  simp [encodeDescription, encodeDescriptionAppend, decodeDescription,
    decodeNat_encodeNatAppend,
    decodeTransitions_encodeTransitions_append]

theorem decodeDescriptionPrefix_encodeDescriptionAppend
    (D : MachineDescription) (suffix : Word MachineCodeSymbol) :
    decodeDescriptionPrefix (encodeDescriptionAppend D suffix) =
      some (D, suffix) := by
  cases D
  simp [encodeDescriptionAppend, decodeDescriptionPrefix,
    decodeNat_encodeNatAppend,
    decodeTransitions_encodeTransitions_append]

theorem decodeDescriptionPrefix_eq_some_encodeDescriptionAppend
    {tokens : Word MachineCodeSymbol} {D : MachineDescription}
    {suffix : Word MachineCodeSymbol}
    (h : decodeDescriptionPrefix tokens = some (D, suffix)) :
    tokens = encodeDescriptionAppend D suffix := by
  cases tokens with
  | nil =>
      cases h
  | cons symbol rest =>
      cases symbol with
      | header =>
          simp [decodeDescriptionPrefix] at h
          cases hstateCount : decodeNat rest with
          | none =>
              simp [hstateCount] at h
          | some parsedStateCount =>
              cases parsedStateCount with
              | mk stateCount restAfterStateCount =>
                  simp [hstateCount] at h
                  cases hstart : decodeNat restAfterStateCount with
                  | none =>
                      simp [hstart] at h
                  | some parsedStart =>
                      cases parsedStart with
                      | mk start restAfterStart =>
                          simp [hstart] at h
                          cases hhalt : decodeNat restAfterStart with
                          | none =>
                              simp [hhalt] at h
                          | some parsedHalt =>
                              cases parsedHalt with
                              | mk halt restAfterHalt =>
                                  simp [hhalt] at h
                                  cases hcount :
                                      decodeNat restAfterHalt with
                                  | none =>
                                      simp [hcount] at h
                                  | some parsedCount =>
                                      cases parsedCount with
                                      | mk transitionCount
                                          restAfterCount =>
                                          simp [hcount] at h
                                          cases htransitions :
                                              decodeTransitions
                                                transitionCount
                                                restAfterCount with
                                          | none =>
                                              simp [htransitions] at h
                                          | some parsedTransitions =>
                                              cases parsedTransitions with
                                              | mk transitions
                                                  parsedSuffix =>
                                                  simp [htransitions] at h
                                                  cases h
                                                  subst D
                                                  subst suffix
                                                  have hstateCountTokens :
                                                      rest =
                                                        encodeNatAppend
                                                          stateCount
                                                          restAfterStateCount :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      hstateCount
                                                  have hstartTokens :
                                                      restAfterStateCount =
                                                        encodeNatAppend start
                                                          restAfterStart :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      hstart
                                                  have hhaltTokens :
                                                      restAfterStart =
                                                        encodeNatAppend halt
                                                          restAfterHalt :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      hhalt
                                                  have hcountTokens :
                                                      restAfterHalt =
                                                        encodeNatAppend
                                                          transitionCount
                                                          restAfterCount :=
                                                    decodeNat_eq_some_encodeNatAppend
                                                      hcount
                                                  have htransitionTokens :
                                                      transitionCount =
                                                          transitions.length ∧
                                                        restAfterCount =
                                                          encodeTransitionsAppend
                                                            transitions
                                                            parsedSuffix :=
                                                    decodeTransitions_eq_some_encodeTransitionsAppend
                                                      htransitions
                                                  simp [encodeDescriptionAppend,
                                                    hstateCountTokens,
                                                    hstartTokens,
                                                    hhaltTokens,
                                                    hcountTokens,
                                                    htransitionTokens.left,
                                                    htransitionTokens.right]
      | transition => cases h
      | tick => cases h
      | done => cases h
      | blank => cases h
      | zero => cases h
      | one => cases h
      | moveLeft => cases h
      | moveRight => cases h

theorem decodeDescriptionPrefix_eq_some_encodeDescription_append
    {tokens : Word MachineCodeSymbol} {D : MachineDescription}
    {suffix : Word MachineCodeSymbol}
    (h : decodeDescriptionPrefix tokens = some (D, suffix)) :
    tokens = List.append (encodeDescription D) suffix := by
  rw [decodeDescriptionPrefix_eq_some_encodeDescriptionAppend h,
    encodeDescriptionAppend_eq_encodeDescription_append]

theorem decodeDescriptionPrefix_encodeDescription_append
    (D : MachineDescription) (suffix : Word MachineCodeSymbol) :
    decodeDescriptionPrefix (List.append (encodeDescription D) suffix) =
      some (D, suffix) := by
  have hword :
      List.append (encodeDescription D) suffix =
        encodeDescriptionAppend D suffix := by
    cases D
    rename_i stateCount start halt transitions
    simpa [encodeDescription, encodeDescriptionAppend, encodeNatAppend,
      List.append_assoc]
      using (encodeTransitionsAppend_append transitions [] suffix)
  rw [hword]
  exact decodeDescriptionPrefix_encodeDescriptionAppend D suffix

/-!
# Description-backed code-word decoder

The universal-machine layer treats both machine descriptions and machine inputs
as words over one code alphabet.  Concrete descriptions still run on Boolean
tapes, so the input code word is first expanded into a Boolean input word.
-/

def encodeCodeSymbolAsInput : MachineCodeSymbol -> Word Bool
  | MachineCodeSymbol.header => [false, false, false, false]
  | MachineCodeSymbol.transition => [false, false, false, true]
  | MachineCodeSymbol.tick => [false, false, true, false]
  | MachineCodeSymbol.done => [false, false, true, true]
  | MachineCodeSymbol.blank => [false, true, false, false]
  | MachineCodeSymbol.zero => [false, true, false, true]
  | MachineCodeSymbol.one => [false, true, true, false]
  | MachineCodeSymbol.moveLeft => [false, true, true, true]
  | MachineCodeSymbol.moveRight => [true, false, false, false]

def encodeCodeWordAsInput : Word MachineCodeSymbol -> Word Bool
  | [] => []
  | symbol :: rest =>
      List.append (encodeCodeSymbolAsInput symbol)
        (encodeCodeWordAsInput rest)

theorem encodeCodeWordAsInput_append
    (pre suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput (List.append pre suffix) =
      List.append (encodeCodeWordAsInput pre)
        (encodeCodeWordAsInput suffix) := by
  induction pre with
  | nil =>
      rfl
  | cons symbol rest ih =>
      simp [encodeCodeWordAsInput]
      exact congrArg
        (fun tail : Word Bool =>
          List.append (encodeCodeSymbolAsInput symbol) tail) ih

theorem encodeCodeWordAsInput_singleton
    (symbol : MachineCodeSymbol) :
    encodeCodeWordAsInput [symbol] =
      encodeCodeSymbolAsInput symbol := by
  cases symbol <;> rfl

def decodeCodeWordAsInput : Word Bool -> Option (Word MachineCodeSymbol)
  | [] => some []
  | false :: false :: false :: false :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.header :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: false :: false :: true :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.transition :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: false :: true :: false :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.tick :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: false :: true :: true :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.done :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: true :: false :: false :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.blank :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: true :: false :: true :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.zero :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: true :: true :: false :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.one :: decoded)
        (decodeCodeWordAsInput rest)
  | false :: true :: true :: true :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.moveLeft :: decoded)
        (decodeCodeWordAsInput rest)
  | true :: false :: false :: false :: rest =>
      Option.map (fun decoded => MachineCodeSymbol.moveRight :: decoded)
        (decodeCodeWordAsInput rest)
  | _ => none

theorem decodeCodeWordAsInput_encodeCodeWordAsInput
    (w : Word MachineCodeSymbol) :
    decodeCodeWordAsInput (encodeCodeWordAsInput w) = some w := by
  induction w with
  | nil =>
      rfl
  | cons symbol rest ih =>
      cases symbol <;>
        simp [encodeCodeWordAsInput, encodeCodeSymbolAsInput,
          decodeCodeWordAsInput, Option.map, ih]

theorem encodeCodeWordAsInput_injective :
    Function.Injective encodeCodeWordAsInput := by
  intro x y h
  have hdecode := congrArg decodeCodeWordAsInput h
  rw [decodeCodeWordAsInput_encodeCodeWordAsInput,
    decodeCodeWordAsInput_encodeCodeWordAsInput] at hdecode
  exact Option.some.inj hdecode

def CodeAccepts
    (machine input : Word MachineCodeSymbol) : Prop :=
  exists D : MachineDescription,
    decodeDescription machine = some D ∧
      D.HaltsOnInput (encodeCodeWordAsInput input)

def CodePrefixAccepts (encoded : Word MachineCodeSymbol) : Prop :=
  exists D : MachineDescription, exists input : Word MachineCodeSymbol,
    decodeDescriptionPrefix encoded = some (D, input) ∧
      D.HaltsOnInput (encodeCodeWordAsInput input)

def CodeAcceptedLanguage
    (machine : Word MachineCodeSymbol) : Language MachineCodeSymbol :=
  fun input => CodeAccepts machine input

def CodePrefixAcceptedLanguage : Language MachineCodeSymbol :=
  fun encoded => CodePrefixAccepts encoded

def EncodedInputLanguage
    (D : MachineDescription) : Language MachineCodeSymbol :=
  fun input => D.HaltsOnInput (encodeCodeWordAsInput input)

theorem codeAccepts_encodeDescription_iff
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    CodeAccepts (encodeDescription D) input <->
      D.HaltsOnInput (encodeCodeWordAsInput input) := by
  constructor
  · intro h
    cases h with
    | intro decoded hdecoded =>
        have henc := decodeDescription_encodeDescription D
        rw [henc] at hdecoded
        cases hdecoded.left
        exact hdecoded.right
  · intro h
    exact Exists.intro D
      (And.intro (decodeDescription_encodeDescription D) h)

theorem codeAccepts_of_encodeDescription
    {D : MachineDescription} {input : Word MachineCodeSymbol}
    (h : D.HaltsOnInput (encodeCodeWordAsInput input)) :
    CodeAccepts (encodeDescription D) input :=
  (codeAccepts_encodeDescription_iff D input).mpr h

theorem codePrefixAccepts_encodeDescription_append_iff
    (D : MachineDescription) (input : Word MachineCodeSymbol) :
    CodePrefixAccepts (List.append (encodeDescription D) input) <->
      D.HaltsOnInput (encodeCodeWordAsInput input) := by
  constructor
  · intro h
    rcases h with ⟨decoded, decodedInput, hdecode, hhalts⟩
    have hprefix :=
      decodeDescriptionPrefix_encodeDescription_append D input
    rw [hprefix] at hdecode
    cases hdecode
    exact hhalts
  · intro h
    exact ⟨D, input,
      decodeDescriptionPrefix_encodeDescription_append D input, h⟩

theorem codePrefixAccepts_of_encodeDescription_append
    {D : MachineDescription} {input : Word MachineCodeSymbol}
    (h : D.HaltsOnInput (encodeCodeWordAsInput input)) :
    CodePrefixAccepts (List.append (encodeDescription D) input) :=
  (codePrefixAccepts_encodeDescription_append_iff D input).mpr h

theorem encodeDescription_codeAccepts_elim
    {D : MachineDescription} {input : Word MachineCodeSymbol}
    (h : CodeAccepts (encodeDescription D) input) :
    D.HaltsOnInput (encodeCodeWordAsInput input) :=
  (codeAccepts_encodeDescription_iff D input).mp h

end MachineDescription

end Computability
end FoC
