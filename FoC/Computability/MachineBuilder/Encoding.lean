import FoC.Computability.MachineBuilder.StateTables

set_option doc.verso true

/-!
# Machine-builder encodings
-/

namespace FoC
namespace Computability

open Languages

namespace MachineDescription

/-!
## Tape and configuration codes

These encodings are over the existing {name}`MachineCodeSymbol` alphabet.  They
are not yet the tape layout used by a universal machine, but they give the
finite simulator target a precise, checked representation of configurations.
-/

def encodeCellsAppend (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  match cells with
  | [] => suffix
  | cell :: rest =>
      encodeCellAppend cell (encodeCellsAppend rest suffix)

def encodeCells (cells : List (Option Bool)) :
    Word MachineCodeSymbol :=
  encodeCellsAppend cells []

def decodeCells : Nat -> Word MachineCodeSymbol ->
    Option (List (Option Bool) × Word MachineCodeSymbol)
  | 0, tokens => some ([], tokens)
  | n + 1, tokens =>
      match decodeCell tokens with
      | none => none
      | some (cell, rest) =>
          match decodeCells n rest with
          | none => none
          | some (cells, suffix) => some (cell :: cells, suffix)

theorem decodeCells_encodeCellsAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    decodeCells cells.length (encodeCellsAppend cells suffix) =
      some (cells, suffix) := by
  induction cells with
  | nil =>
      rfl
  | cons cell rest ih =>
      simp [encodeCellsAppend, decodeCells, decodeCell_encodeCellAppend, ih]

theorem decodeCells_eq_some_encodeCellsAppend
    {len : Nat} {tokens : Word MachineCodeSymbol}
    {cells : List (Option Bool)} {suffix : Word MachineCodeSymbol}
    (h : decodeCells len tokens = some (cells, suffix)) :
    len = cells.length ∧ tokens = encodeCellsAppend cells suffix := by
  induction len generalizing tokens cells suffix with
  | zero =>
      simp [decodeCells] at h
      cases h
      subst cells
      subst tokens
      constructor <;> rfl
  | succ len ih =>
      simp [decodeCells] at h
      cases hcell : decodeCell tokens with
      | none =>
          simp [hcell] at h
      | some parsedCell =>
          cases parsedCell with
          | mk cell rest =>
              simp [hcell] at h
              cases hrest : decodeCells len rest with
              | none =>
                  simp [hrest] at h
              | some parsedRest =>
                  cases parsedRest with
                  | mk tail parsedSuffix =>
                      simp [hrest] at h
                      cases h
                      subst cells
                      subst suffix
                      have hcellTokens :
                          tokens = encodeCellAppend cell rest :=
                        decodeCell_eq_some_encodeCellAppend hcell
                      have htail :
                          len = tail.length ∧
                            rest = encodeCellsAppend tail parsedSuffix :=
                        ih hrest
                      constructor
                      · simp [htail.left]
                      · simp [encodeCellsAppend, hcellTokens,
                          htail.right]

def encodeCellListAppend (cells : List (Option Bool))
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeNatAppend cells.length (encodeCellsAppend cells suffix)

def decodeCellList (tokens : Word MachineCodeSymbol) :
    Option (List (Option Bool) × Word MachineCodeSymbol) :=
  match decodeNat tokens with
  | none => none
  | some (len, rest) => decodeCells len rest

theorem decodeCellList_encodeCellListAppend
    (cells : List (Option Bool)) (suffix : Word MachineCodeSymbol) :
    decodeCellList (encodeCellListAppend cells suffix) =
      some (cells, suffix) := by
  simp [decodeCellList, encodeCellListAppend, decodeNat_encodeNatAppend,
    decodeCells_encodeCellsAppend]

theorem decodeCellList_eq_some_encodeCellListAppend
    {tokens : Word MachineCodeSymbol}
    {cells : List (Option Bool)} {suffix : Word MachineCodeSymbol}
    (h : decodeCellList tokens = some (cells, suffix)) :
    tokens = encodeCellListAppend cells suffix := by
  unfold decodeCellList at h
  cases hlen : decodeNat tokens with
  | none =>
      simp [hlen] at h
  | some parsedLen =>
      cases parsedLen with
      | mk len rest =>
          simp [hlen] at h
          cases hcells : decodeCells len rest with
          | none =>
              simp [hcells] at h
          | some parsedCells =>
              cases parsedCells with
              | mk decodedCells decodedSuffix =>
                  simp [hcells] at h
                  cases h
                  subst cells
                  subst suffix
                  have htokens :
                      tokens = encodeNatAppend len rest :=
                    decodeNat_eq_some_encodeNatAppend hlen
                  have hrest :
                      len = decodedCells.length ∧
                        rest =
                          encodeCellsAppend decodedCells decodedSuffix :=
                    decodeCells_eq_some_encodeCellsAppend hcells
                  rw [htokens, hrest.left, hrest.right]
                  rfl

def encodeTapeAppend (T : Tape Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeCellListAppend T.left
    (encodeCellAppend T.head
      (encodeCellListAppend T.right suffix))

def encodeTape (T : Tape Bool) : Word MachineCodeSymbol :=
  encodeTapeAppend T []

def decodeTape (tokens : Word MachineCodeSymbol) :
    Option (Tape Bool × Word MachineCodeSymbol) :=
  match decodeCellList tokens with
  | none => none
  | some (left, rest) =>
      match decodeCell rest with
      | none => none
      | some (head, rest) =>
          match decodeCellList rest with
          | none => none
          | some (right, suffix) =>
              some ({ left := left, head := head, right := right }, suffix)

theorem decodeTape_encodeTapeAppend
    (T : Tape Bool) (suffix : Word MachineCodeSymbol) :
    decodeTape (encodeTapeAppend T suffix) = some (T, suffix) := by
  cases T
  simp [encodeTapeAppend, decodeTape, decodeCellList_encodeCellListAppend,
    decodeCell_encodeCellAppend]

theorem decodeTape_encodeTape (T : Tape Bool) :
    decodeTape (encodeTape T) = some (T, []) :=
  decodeTape_encodeTapeAppend T []

theorem decodeTape_eq_some_encodeTapeAppend
    {tokens : Word MachineCodeSymbol} {T : Tape Bool}
    {suffix : Word MachineCodeSymbol}
    (h : decodeTape tokens = some (T, suffix)) :
    tokens = encodeTapeAppend T suffix := by
  unfold decodeTape at h
  cases hleft : decodeCellList tokens with
  | none =>
      simp [hleft] at h
  | some parsedLeft =>
      cases parsedLeft with
      | mk left restAfterLeft =>
          simp [hleft] at h
          cases hhead : decodeCell restAfterLeft with
          | none =>
              simp [hhead] at h
          | some parsedHead =>
              cases parsedHead with
              | mk head restAfterHead =>
                  simp [hhead] at h
                  cases hright : decodeCellList restAfterHead with
                  | none =>
                      simp [hright] at h
                  | some parsedRight =>
                      cases parsedRight with
                      | mk right parsedSuffix =>
                          simp [hright] at h
                          cases h
                          subst T
                          subst suffix
                          have htokens :
                              tokens =
                                encodeCellListAppend left
                                  restAfterLeft :=
                            decodeCellList_eq_some_encodeCellListAppend
                              hleft
                          have hrestAfterLeft :
                              restAfterLeft =
                                encodeCellAppend head restAfterHead :=
                            decodeCell_eq_some_encodeCellAppend hhead
                          have hrestAfterHead :
                              restAfterHead =
                                encodeCellListAppend right parsedSuffix :=
                            decodeCellList_eq_some_encodeCellListAppend
                              hright
                          simp [encodeTapeAppend, htokens,
                            hrestAfterLeft, hrestAfterHead]

def encodeConfigurationAppend (c : Configuration)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeNatAppend c.state (encodeTapeAppend c.tape suffix)

def encodeConfiguration (c : Configuration) :
    Word MachineCodeSymbol :=
  encodeConfigurationAppend c []

def decodeConfiguration (tokens : Word MachineCodeSymbol) :
    Option (Configuration × Word MachineCodeSymbol) :=
  match decodeNat tokens with
  | none => none
  | some (state, rest) =>
      match decodeTape rest with
      | none => none
      | some (tape, suffix) =>
          some ({ state := state, tape := tape }, suffix)

theorem decodeConfiguration_encodeConfigurationAppend
    (c : Configuration) (suffix : Word MachineCodeSymbol) :
    decodeConfiguration (encodeConfigurationAppend c suffix) =
      some (c, suffix) := by
  cases c
  simp [encodeConfigurationAppend, decodeConfiguration,
    decodeNat_encodeNatAppend, decodeTape_encodeTapeAppend]

theorem decodeConfiguration_encodeConfiguration (c : Configuration) :
    decodeConfiguration (encodeConfiguration c) = some (c, []) :=
  decodeConfiguration_encodeConfigurationAppend c []

theorem decodeConfiguration_eq_some_encodeConfigurationAppend
    {tokens : Word MachineCodeSymbol} {c : Configuration}
    {suffix : Word MachineCodeSymbol}
    (h : decodeConfiguration tokens = some (c, suffix)) :
    tokens = encodeConfigurationAppend c suffix := by
  unfold decodeConfiguration at h
  cases hstate : decodeNat tokens with
  | none =>
      simp [hstate] at h
  | some parsedState =>
      cases parsedState with
      | mk state restAfterState =>
          simp [hstate] at h
          cases htape : decodeTape restAfterState with
          | none =>
              simp [htape] at h
          | some parsedTape =>
              cases parsedTape with
              | mk tape parsedSuffix =>
                  simp [htape] at h
                  cases h
                  subst c
                  subst suffix
                  have htokens :
                      tokens = encodeNatAppend state restAfterState :=
                    decodeNat_eq_some_encodeNatAppend hstate
                  have hrest :
                      restAfterState =
                        encodeTapeAppend tape parsedSuffix :=
                    decodeTape_eq_some_encodeTapeAppend htape
                  simp [encodeConfigurationAppend, htokens, hrest]

theorem decodeConfiguration_eq_some_encodeConfiguration
    {tokens : Word MachineCodeSymbol} {c : Configuration}
    (h : decodeConfiguration tokens = some (c, [])) :
    tokens = encodeConfiguration c := by
  simpa [encodeConfiguration] using
    decodeConfiguration_eq_some_encodeConfigurationAppend h

def runEncodedConfiguration
    (D : MachineDescription) (steps : Nat)
    (tokens : Word MachineCodeSymbol) :
    Option (Configuration × Word MachineCodeSymbol) :=
  match decodeConfiguration tokens with
  | none => none
  | some (c, suffix) => some (D.runConfig steps c, suffix)

def checksEncodedRun
    (D : MachineDescription)
    (start : Word MachineCodeSymbol)
    (steps : Nat)
    (finish : Word MachineCodeSymbol) : Bool :=
  match decodeConfiguration start, decodeConfiguration finish with
  | some (c, []), some (finished, []) =>
      D.runConfig steps c == finished
  | _, _ => false

theorem runEncodedConfiguration_encodeConfigurationAppend
    (D : MachineDescription) (steps : Nat)
    (c : Configuration) (suffix : Word MachineCodeSymbol) :
    runEncodedConfiguration D steps
        (encodeConfigurationAppend c suffix) =
      some (D.runConfig steps c, suffix) := by
  simp [runEncodedConfiguration,
    decodeConfiguration_encodeConfigurationAppend]

theorem runEncodedConfiguration_encodeConfiguration
    (D : MachineDescription) (steps : Nat)
    (c : Configuration) :
    runEncodedConfiguration D steps (encodeConfiguration c) =
      some (D.runConfig steps c, []) :=
  runEncodedConfiguration_encodeConfigurationAppend D steps c []

theorem checksEncodedRun_encodeConfiguration
    (D : MachineDescription) (steps : Nat)
    (c : Configuration) :
    checksEncodedRun D
        (encodeConfiguration c)
        steps
        (encodeConfiguration (D.runConfig steps c)) = true := by
  simp [checksEncodedRun, decodeConfiguration_encodeConfiguration]

def stepConfigurationCode
    (D : MachineDescription)
    (tokens : Word MachineCodeSymbol) :
    Option (Word MachineCodeSymbol) :=
  match decodeConfiguration tokens with
  | some (c, []) => some (encodeConfiguration (D.runConfig 1 c))
  | _ => none

theorem stepConfigurationCode_encodeConfiguration
    (D : MachineDescription) (c : Configuration) :
    stepConfigurationCode D (encodeConfiguration c) =
      some (encodeConfiguration (D.runConfig 1 c)) := by
  simp [stepConfigurationCode, decodeConfiguration_encodeConfiguration]

theorem runConfig_one_of_lookupTransition_none
    {D : MachineDescription} {c : Configuration}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = none) :
    D.runConfig 1 c = c := by
  cases c
  simp [runConfig, stepConfig, hlookup]

theorem runConfig_one_of_lookupTransition_some
    {D : MachineDescription} {c : Configuration}
    {t : TransitionDescription}
    (hlookup :
      D.lookupTransition c.state (Tape.read c.tape) = some t) :
    D.runConfig 1 c =
      { state := t.target
        tape := Tape.move t.move (Tape.write t.write c.tape) } := by
  cases c
  simp [runConfig, stepConfig, hlookup]

/-!
## Canonical simulator layouts

The transition-level simulator needs one fixed work-tape convention.  The
logical layout is first written as a word over {name}`MachineCodeSymbol`; the
actual Boolean machine tape then uses the existing fixed-width Boolean
expansion from {module}`FoC.Computability.Encoding`.

The single-simulator layout stores the original input, the current stage, the
simulated configuration, and a hit flag.  The paired dovetail layout stores the
same input and stage together with the two simulated configurations and their
accumulated hit flags.
-/

def encodeBoolAppend (b : Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeCellAppend (some b) suffix

def decodeBool (tokens : Word MachineCodeSymbol) :
    Option (Bool × Word MachineCodeSymbol) :=
  match decodeCell tokens with
  | some (some b, suffix) => some (b, suffix)
  | _ => none

theorem decodeBool_encodeBoolAppend
    (b : Bool) (suffix : Word MachineCodeSymbol) :
    decodeBool (encodeBoolAppend b suffix) = some (b, suffix) := by
  cases b <;> rfl

theorem decodeBool_eq_some_encodeBoolAppend
    {tokens : Word MachineCodeSymbol} {b : Bool}
    {suffix : Word MachineCodeSymbol}
    (h : decodeBool tokens = some (b, suffix)) :
    tokens = encodeBoolAppend b suffix := by
  unfold decodeBool at h
  cases hcell : decodeCell tokens with
  | none =>
      simp [hcell] at h
  | some parsed =>
      cases parsed with
      | mk cell parsedSuffix =>
          cases cell with
          | none =>
              simp [hcell] at h
          | some decoded =>
              simp [hcell] at h
              cases h
              subst decoded
              subst parsedSuffix
              exact decodeCell_eq_some_encodeCellAppend hcell

def cellsToWord? : List (Option Bool) -> Option (Word Bool)
  | [] => some []
  | none :: _ => none
  | some b :: rest =>
      match cellsToWord? rest with
      | none => none
      | some w => some (b :: w)

theorem cellsToWord?_map_some (w : Word Bool) :
    cellsToWord? (w.map some) = some w := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      simp [cellsToWord?, ih]

theorem cellsToWord?_eq_some_iff
    {cells : List (Option Bool)} {w : Word Bool} :
    cellsToWord? cells = some w <-> cells = w.map some := by
  constructor
  · intro h
    induction cells generalizing w with
    | nil =>
        cases w with
        | nil =>
            rfl
        | cons b rest =>
            simp [cellsToWord?] at h
    | cons cell rest ih =>
        cases cell with
        | none =>
            simp [cellsToWord?] at h
        | some b =>
            cases hrest : cellsToWord? rest with
            | none =>
                simp [cellsToWord?, hrest] at h
            | some tail =>
                simp [cellsToWord?, hrest] at h
                cases h
                have htail : rest = tail.map some := ih hrest
                simp [htail]
  · intro h
    rw [h]
    exact cellsToWord?_map_some w

def encodeBoolWordAppend (w : Word Bool)
    (suffix : Word MachineCodeSymbol) : Word MachineCodeSymbol :=
  encodeCellListAppend (w.map some) suffix

def encodeBoolWord (w : Word Bool) : Word MachineCodeSymbol :=
  encodeBoolWordAppend w []

def decodeBoolWord (tokens : Word MachineCodeSymbol) :
    Option (Word Bool × Word MachineCodeSymbol) :=
  match decodeCellList tokens with
  | none => none
  | some (cells, suffix) =>
      match cellsToWord? cells with
      | none => none
      | some w => some (w, suffix)

theorem decodeBoolWord_encodeBoolWordAppend
    (w : Word Bool) (suffix : Word MachineCodeSymbol) :
    decodeBoolWord (encodeBoolWordAppend w suffix) =
      some (w, suffix) := by
  simp [decodeBoolWord, encodeBoolWordAppend,
    decodeCellList_encodeCellListAppend, cellsToWord?_map_some]

theorem decodeBoolWord_encodeBoolWord (w : Word Bool) :
    decodeBoolWord (encodeBoolWord w) = some (w, []) := by
  simpa [encodeBoolWord] using
    decodeBoolWord_encodeBoolWordAppend w []

theorem decodeBoolWord_eq_some_encodeBoolWordAppend
    {tokens : Word MachineCodeSymbol}
    {w : Word Bool} {suffix : Word MachineCodeSymbol}
    (h : decodeBoolWord tokens = some (w, suffix)) :
    tokens = encodeBoolWordAppend w suffix := by
  unfold decodeBoolWord at h
  cases hcells : decodeCellList tokens with
  | none =>
      simp [hcells] at h
  | some parsed =>
      cases parsed with
      | mk cells parsedSuffix =>
          simp [hcells] at h
          cases hword : cellsToWord? cells with
          | none =>
              simp [hword] at h
          | some decoded =>
              simp [hword] at h
              cases h
              subst decoded
              subst parsedSuffix
              have htokens : tokens = encodeCellListAppend cells suffix :=
                decodeCellList_eq_some_encodeCellListAppend hcells
              have hcellsEq : cells = w.map some :=
                cellsToWord?_eq_some_iff.mp hword
              simp [encodeBoolWordAppend, htokens, hcellsEq]

theorem encodeBoolWord_injective :
    Function.Injective encodeBoolWord := by
  intro w v h
  have hdecode :
      decodeBoolWord (encodeBoolWord w) =
        decodeBoolWord (encodeBoolWord v) := by
    rw [h]
  rw [decodeBoolWord_encodeBoolWord w,
    decodeBoolWord_encodeBoolWord v] at hdecode
  cases hdecode
  rfl


end MachineDescription

end Computability
end FoC
