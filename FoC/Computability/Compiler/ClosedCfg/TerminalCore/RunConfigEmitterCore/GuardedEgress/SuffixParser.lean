import FoC.Computability.Compiler.ClosedCfg.TerminalCore.RunConfigEmitterCore.GuardedEgress.WitnessBridge
import FoC.Computability.Compiler.Structured.Lowering.FiniteMachineTactics

set_option doc.verso true

/-!
# Guarded metadata-witness suffix parser

This fixed table consumes the guarded metadata suffix after the tape-field
serializer.  It preserves the raw metadata tokens, removes the exhausted
scratch/hit/witness framing, and preserves the known branch's unary state
tokens.  Four transition-free exits retain both the known/other branch and the
decoded hit bit for the downstream normalizer.
-/

namespace FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
namespace GuardedEgress.MetadataWitnessSuffixParser

open Languages MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open MetadataTokenCopy

def stateByHit (base : Nat) : Bool -> Nat
  | false => base
  | true => base + 1

def knownFalseExit : Nat := 59
def knownTrueExit : Nat := 60
def otherFalseExit : Nat := 61
def otherTrueExit : Nat := 62

def knownExitState : Bool -> Nat
  | false => knownFalseExit
  | true => knownTrueExit

def otherExitState : Bool -> Nat
  | false => otherFalseExit
  | true => otherTrueExit

/-!
The shared states are 0--10.  Paired states beginning at 11 carry the hit bit;
the four exits are 59--62, state 63 crosses the opening boundary, and the
unused public halt is 64.
-/

def branchTransitions (hit : Bool) : List TransitionDescription :=
  [ transition (stateByHit 11 hit) (some false) none Direction.right
      (stateByHit 13 hit)
  , transition (stateByHit 13 hit) (some false) none Direction.right
      (stateByHit 15 hit)

  , transition (stateByHit 15 hit) (some false) none Direction.right
      (stateByHit 17 hit)
  , transition (stateByHit 17 hit) (some true) none Direction.right
      (stateByHit 19 hit)
  , transition (stateByHit 19 hit) (some true) none Direction.right
      (stateByHit 21 hit)
  , transition (stateByHit 21 hit) (some false) none Direction.right
      (stateByHit 23 hit)

  , transition (stateByHit 23 hit) (some true) none Direction.right
      (stateByHit 25 hit)
  , transition (stateByHit 23 hit) (some false) none Direction.right
      (stateByHit 31 hit)

  , transition (stateByHit 25 hit) (some false) none Direction.right
      (stateByHit 27 hit)
  , transition (stateByHit 27 hit) (some false) none Direction.right
      (stateByHit 29 hit)
  , transition (stateByHit 29 hit) (some true) none Direction.right
      (stateByHit 37 hit)

  , transition (stateByHit 31 hit) (some true) none Direction.right
      (stateByHit 33 hit)
  , transition (stateByHit 33 hit) (some true) none Direction.right
      (stateByHit 35 hit)
  , transition (stateByHit 35 hit) (some false) none Direction.right
      (stateByHit 51 hit)

  , transition (stateByHit 37 hit) (some false) (some false)
      Direction.right (stateByHit 39 hit)
  , transition (stateByHit 37 hit) (some true) (some true)
      Direction.right (stateByHit 41 hit)
  , transition (stateByHit 39 hit) (some true) (some true)
      Direction.right (stateByHit 37 hit)
  , transition (stateByHit 39 hit) (some false) none
      Direction.left (stateByHit 43 hit)
  , transition (stateByHit 41 hit) (some false) (some false)
      Direction.right (stateByHit 37 hit)
  , transition (stateByHit 43 hit) (some false) none
      Direction.right (stateByHit 45 hit)
  , transition (stateByHit 45 hit) none none Direction.right
      (stateByHit 47 hit)

  , transition (stateByHit 47 hit) (some false) none Direction.right
      (stateByHit 49 hit)
  , transition (stateByHit 49 hit) (some false) none Direction.right
      (knownExitState hit)

  , transition (stateByHit 51 hit) (some false) none Direction.right
      (stateByHit 53 hit)
  , transition (stateByHit 53 hit) (some false) none Direction.right
      (stateByHit 55 hit)
  , transition (stateByHit 55 hit) (some false) none Direction.right
      (stateByHit 57 hit)
  , transition (stateByHit 57 hit) (some false) none Direction.right
      (otherExitState hit) ]

def description : MachineDescription where
  stateCount := 65
  start := 0
  halt := 64
  transitions :=
    [ transition 0 (some false) none Direction.right 63
    , transition 63 (some false) (some false) Direction.right 1

    , transition 1 (some false) (some false) Direction.right 2
    , transition 1 (some true) (some true) Direction.right 3
    , transition 2 (some true) (some true) Direction.right 1
    , transition 2 (some false) none Direction.left 4
    , transition 3 (some false) (some false) Direction.right 1
    , transition 4 (some false) none Direction.right 5
    , transition 5 none none Direction.right 6

    , transition 6 (some true) none Direction.right 7
    , transition 7 (some false) none Direction.right 6
    , transition 7 (some true) none Direction.right 8

    , transition 8 (some false) none Direction.right 9
    , transition 8 (some true) none Direction.right 10
    , transition 9 (some true) none Direction.right (stateByHit 11 false)
    , transition 10 (some false) none Direction.right (stateByHit 11 true) ] ++
      [false, true].flatMap branchTransitions

set_option maxRecDepth 100000 in
theorem description_subroutineReady : description.SubroutineReady :=
  machineDescription_subroutineReady_of_transition_checks
    description (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem description_transitionFreeAt_knownFalseExit :
    description.TransitionFreeAt knownFalseExit :=
  transition_notFrom_of_all
    (l := description.transitions) (state := knownFalseExit) (by decide)

theorem description_transitionFreeAt_knownTrueExit :
    description.TransitionFreeAt knownTrueExit :=
  transition_notFrom_of_all
    (l := description.transitions) (state := knownTrueExit) (by decide)

theorem description_transitionFreeAt_otherFalseExit :
    description.TransitionFreeAt otherFalseExit :=
  transition_notFrom_of_all
    (l := description.transitions) (state := otherFalseExit) (by decide)

theorem description_transitionFreeAt_otherTrueExit :
    description.TransitionFreeAt otherTrueExit :=
  transition_notFrom_of_all
    (l := description.transitions) (state := otherTrueExit) (by decide)

theorem description_transitionFreeAt_knownExit (hit : Bool) :
    description.TransitionFreeAt (knownExitState hit) := by
  cases hit
  · exact description_transitionFreeAt_knownFalseExit
  · exact description_transitionFreeAt_knownTrueExit

theorem description_transitionFreeAt_otherExit (hit : Bool) :
    description.TransitionFreeAt (otherExitState hit) := by
  cases hit
  · exact description_transitionFreeAt_otherFalseExit
  · exact description_transitionFreeAt_otherTrueExit

def sourceTape
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (hit : Bool)
    (witness right : List (Option Bool)) : Tape Bool :=
  tapeAtCells left
    (List.append [some false, some false]
      (List.append (MetadataTokenCopy.encodedTokens raw)
        (List.append [some false, some false]
          (List.append
            (logicalCellListCode
              (List.replicate scratchCount (some true)))
            (List.append [some true, some true]
              (List.append (logicalCellCode (some hit))
                (List.append [some false, some false]
                  (List.append witness
                    (List.append
                      [some false, some false, some false, some false]
                      (none :: right))))))))))

def knownTargetTape
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (q : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append (List.replicate 4 (none : Option Bool))
      (List.append
        (MetadataTokenCopy.encodedTokens
          (MetadataWitnessBridge.natTokens q)).reverse
        (List.append
          (List.replicate (16 + 2 * scratchCount) none)
          (List.append (MetadataTokenCopy.encodedTokens raw).reverse
            (some false :: none :: left)))))
    (none :: right)

def otherTargetTape
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat)
    (right : List (Option Bool)) : Tape Bool :=
  tapeAtCells
    (List.append
      (List.replicate (20 + 2 * scratchCount) (none : Option Bool))
      (List.append (MetadataTokenCopy.encodedTokens raw).reverse
        (some false :: none :: left)))
    (none :: right)

private theorem run_open
    (left suffix : List (Option Bool)) :
    description.runConfig 2
        { state := description.start
          tape := tapeAtCells left
            (some false :: some false :: suffix) } =
      { state := 1
        tape := tapeAtCells (some false :: none :: left) suffix } := by
  cases suffix <;>
    machine_step [description, branchTransitions, stateByHit]

private theorem run_raw_token
    (kind : MetadataTokenCopy.TokenKind)
    (left suffix : List (Option Bool)) :
    description.runConfig 8
        { state := 1
          tape := tapeAtCells left
            (List.append (MetadataTokenCopy.encodedTokenCells kind)
              suffix) } =
      { state := 1
        tape := tapeAtCells
          (List.append
            (MetadataTokenCopy.encodedTokenCells kind).reverse left)
          suffix } := by
  cases kind <;> cases suffix <;>
    machine_step [description, branchTransitions, stateByHit,
      MetadataTokenCopy.encodedTokenCells,
      MetadataTokenCopy.TokenKind.bits, logicalCellListBits,
      logicalCellBits]

private theorem run_raw_tokens
    (tokens : List MetadataTokenCopy.TokenKind)
    (left suffix : List (Option Bool)) :
    description.runConfig (8 * tokens.length)
        { state := 1
          tape := tapeAtCells left
            (List.append (MetadataTokenCopy.encodedTokens tokens) suffix) } =
      { state := 1
        tape := tapeAtCells
          (List.append
            (MetadataTokenCopy.encodedTokens tokens).reverse left)
          suffix } := by
  induction tokens generalizing left with
  | nil =>
      rfl
  | cons kind rest ih =>
      rw [show 8 * (kind :: rest).length = 8 + 8 * rest.length by
        simp; lia]
      rw [MachineDescription.runConfig_add]
      have hsource :
          List.append (MetadataTokenCopy.encodedTokens (kind :: rest)) suffix =
            List.append (MetadataTokenCopy.encodedTokenCells kind)
              (List.append (MetadataTokenCopy.encodedTokens rest) suffix) := by
        rw [MetadataTokenCopy.encodedTokens_cons]
        exact List.append_assoc _ _ _
      rw [hsource]
      rw [run_raw_token]
      rw [ih]
      simp [List.reverse_append, List.append_assoc]

private theorem run_raw_delimiter
    (left suffix : List (Option Bool)) :
    description.runConfig 4
        { state := 1
          tape := tapeAtCells left
            (some false :: some false :: suffix) } =
      { state := 6
        tape := tapeAtCells (none :: none :: left) suffix } := by
  cases suffix <;>
    machine_step [description, branchTransitions, stateByHit]

private theorem run_scratch_cell
    (left suffix : List (Option Bool)) :
    description.runConfig 2
        { state := 6
          tape := tapeAtCells left
            (List.append (logicalCellCode (some true)) suffix) } =
      { state := 6
        tape := tapeAtCells (none :: none :: left) suffix } := by
  cases suffix <;>
    machine_step [description, branchTransitions, stateByHit,
      logicalCellCode]

private theorem run_scratch
    (n : Nat) (left suffix : List (Option Bool)) :
    description.runConfig (2 * n)
        { state := 6
          tape := tapeAtCells left
            (List.append
              (logicalCellListCode (List.replicate n (some true)))
              suffix) } =
      { state := 6
        tape := tapeAtCells
          (List.append (List.replicate (2 * n) none) left) suffix } := by
  induction n generalizing left with
  | zero =>
      rfl
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 + 2 * n by lia]
      rw [MachineDescription.runConfig_add]
      have hsource :
          List.append
              (logicalCellListCode
                (List.replicate (n + 1) (some true))) suffix =
            List.append (logicalCellCode (some true))
              (List.append
                (logicalCellListCode
                  (List.replicate n (some true))) suffix) := by
        rw [show n + 1 = Nat.succ n by lia]
        rw [List.replicate_succ, logicalCellListCode_cons]
        exact List.append_assoc _ _ _
      rw [hsource]
      rw [run_scratch_cell]
      rw [ih]
      have hleft :
          List.append (List.replicate (2 * n) none) (none :: none :: left) =
            List.append (List.replicate (2 + 2 * n) none) left := by
        rw [show 2 + 2 * n = 2 * n + 2 by lia]
        simpa using
          (FoC.Computability.list_replicate_add_append
            (none : Option Bool) (2 * n) 2 left).symm
      rw [hleft]

private theorem run_head_marker
    (left suffix : List (Option Bool)) :
    description.runConfig 2
        { state := 6
          tape := tapeAtCells left
            (some true :: some true :: suffix) } =
      { state := 8
        tape := tapeAtCells (none :: none :: left) suffix } := by
  cases suffix <;>
    machine_step [description, branchTransitions, stateByHit]

private theorem run_hit_separator
    (hit : Bool) (left suffix : List (Option Bool)) :
    description.runConfig 4
        { state := 8
          tape := tapeAtCells left
            (List.append (logicalCellCode (some hit))
              (some false :: some false :: suffix)) } =
      { state := stateByHit 15 hit
        tape := tapeAtCells
          (List.replicate 4 (none : Option Bool) ++ left) suffix } := by
  cases hit <;> cases suffix <;>
    machine_step [description, branchTransitions, stateByHit,
      logicalCellCode]

private theorem run_known_tag
    (hit : Bool) (left suffix : List (Option Bool)) :
    description.runConfig 8
        { state := stateByHit 15 hit
          tape := tapeAtCells left
            (List.append
              (MetadataTokenCopy.encodedTokenCells .one) suffix) } =
      { state := stateByHit 37 hit
        tape := tapeAtCells
          (List.append (List.replicate 8 none) left) suffix } := by
  cases hit <;> cases suffix <;>
    machine_step [description, branchTransitions, stateByHit,
      knownExitState, knownFalseExit, knownTrueExit,
      otherExitState, otherFalseExit, otherTrueExit,
      MetadataTokenCopy.encodedTokenCells,
      MetadataTokenCopy.TokenKind.bits, logicalCellListBits,
      logicalCellBits]

private theorem run_other_tag
    (hit : Bool) (left suffix : List (Option Bool)) :
    description.runConfig 8
        { state := stateByHit 15 hit
          tape := tapeAtCells left
            (List.append
              (MetadataTokenCopy.encodedTokenCells .zero) suffix) } =
      { state := stateByHit 51 hit
        tape := tapeAtCells
          (List.append (List.replicate 8 none) left) suffix } := by
  cases hit <;> cases suffix <;>
    machine_step [description, branchTransitions, stateByHit,
      knownExitState, knownFalseExit, knownTrueExit,
      otherExitState, otherFalseExit, otherTrueExit,
      MetadataTokenCopy.encodedTokenCells,
      MetadataTokenCopy.TokenKind.bits, logicalCellListBits,
      logicalCellBits]

private theorem run_known_token
    (hit : Bool) (kind : MetadataTokenCopy.TokenKind)
    (left suffix : List (Option Bool)) :
    description.runConfig 8
        { state := stateByHit 37 hit
          tape := tapeAtCells left
            (List.append (MetadataTokenCopy.encodedTokenCells kind)
              suffix) } =
      { state := stateByHit 37 hit
        tape := tapeAtCells
          (List.append
            (MetadataTokenCopy.encodedTokenCells kind).reverse left)
          suffix } := by
  cases hit <;> cases kind <;> cases suffix <;>
    machine_step [description, branchTransitions, stateByHit,
      knownExitState, knownFalseExit, knownTrueExit,
      otherExitState, otherFalseExit, otherTrueExit,
      MetadataTokenCopy.encodedTokenCells,
      MetadataTokenCopy.TokenKind.bits, logicalCellListBits,
      logicalCellBits]

private theorem run_known_tokens
    (hit : Bool) (tokens : List MetadataTokenCopy.TokenKind)
    (left suffix : List (Option Bool)) :
    description.runConfig (8 * tokens.length)
        { state := stateByHit 37 hit
          tape := tapeAtCells left
            (List.append (MetadataTokenCopy.encodedTokens tokens) suffix) } =
      { state := stateByHit 37 hit
        tape := tapeAtCells
          (List.append
            (MetadataTokenCopy.encodedTokens tokens).reverse left)
          suffix } := by
  induction tokens generalizing left with
  | nil =>
      rfl
  | cons kind rest ih =>
      rw [show 8 * (kind :: rest).length = 8 + 8 * rest.length by
        simp; lia]
      rw [MachineDescription.runConfig_add]
      have hsource :
          List.append (MetadataTokenCopy.encodedTokens (kind :: rest)) suffix =
            List.append (MetadataTokenCopy.encodedTokenCells kind)
              (List.append (MetadataTokenCopy.encodedTokens rest) suffix) := by
        rw [MetadataTokenCopy.encodedTokens_cons]
        exact List.append_assoc _ _ _
      rw [hsource]
      rw [run_known_token]
      rw [ih]
      simp [MetadataTokenCopy.encodedTokens_cons,
        List.reverse_append, List.append_assoc]

private theorem run_known_final
    (hit : Bool) (left right : List (Option Bool)) :
    description.runConfig 6
        { state := stateByHit 37 hit
          tape := tapeAtCells left
            (some false :: some false :: some false :: some false ::
              none :: right) } =
      { state := knownExitState hit
        tape := tapeAtCells
          (List.append (List.replicate 4 none) left) (none :: right) } := by
  cases hit <;> cases right <;>
    machine_step [description, branchTransitions, stateByHit,
      knownExitState, knownFalseExit, knownTrueExit,
      otherExitState, otherFalseExit, otherTrueExit]

private theorem run_other_final
    (hit : Bool) (left right : List (Option Bool)) :
    description.runConfig 4
        { state := stateByHit 51 hit
          tape := tapeAtCells left
            (some false :: some false :: some false :: some false ::
              none :: right) } =
      { state := otherExitState hit
        tape := tapeAtCells
          (List.append (List.replicate 4 none) left) (none :: right) } := by
  cases hit <;> cases right <;>
    machine_step [description, branchTransitions, stateByHit,
      knownExitState, knownFalseExit, knownTrueExit,
      otherExitState, otherFalseExit, otherTrueExit]

theorem run_known
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (hit : Bool) (q : Nat)
    (right : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
          { state := description.start
            tape := sourceTape left raw scratchCount hit
              (List.append (MetadataTokenCopy.encodedTokenCells .one)
                (MetadataTokenCopy.encodedTokens
                  (MetadataWitnessBridge.natTokens q)))
              right } =
        { state := knownExitState hit
          tape := knownTargetTape left raw scratchCount q right } := by
  refine ⟨2 +
      (8 * raw.length +
        (4 +
          (2 * scratchCount +
            (2 +
              (4 +
                (8 +
                  (8 * (MetadataWitnessBridge.natTokens q).length +
                    6))))))), ?_⟩
  unfold sourceTape
  simp only [List.append]
  rw [MachineDescription.runConfig_add]
  rw [run_open]
  rw [MachineDescription.runConfig_add]
  rw [run_raw_tokens]
  rw [MachineDescription.runConfig_add]
  rw [run_raw_delimiter]
  rw [MachineDescription.runConfig_add]
  rw [run_scratch]
  rw [MachineDescription.runConfig_add]
  rw [run_head_marker]
  rw [MachineDescription.runConfig_add]
  rw [run_hit_separator]
  rw [MachineDescription.runConfig_add]
  have hknownSource :
      List.append
          (List.append (MetadataTokenCopy.encodedTokenCells .one)
            (MetadataTokenCopy.encodedTokens
              (MetadataWitnessBridge.natTokens q)))
          (some false :: some false :: some false :: some false ::
            none :: right) =
        List.append (MetadataTokenCopy.encodedTokenCells .one)
          (List.append
            (MetadataTokenCopy.encodedTokens
              (MetadataWitnessBridge.natTokens q))
            (some false :: some false :: some false :: some false ::
              none :: right)) := by
    exact List.append_assoc _ _ _
  rw [hknownSource]
  rw [run_known_tag]
  rw [MachineDescription.runConfig_add]
  rw [run_known_tokens]
  rw [run_known_final]
  have hblanks (tail : List (Option Bool)) :
      List.append (List.replicate 8 none)
          (List.append (List.replicate 4 none)
            (none :: none ::
              List.append (List.replicate (2 * scratchCount) none)
                (none :: none :: tail))) =
        List.append (List.replicate (16 + 2 * scratchCount) none)
          tail := by
    change
      List.append (List.replicate 8 none)
          (List.append (List.replicate 4 none)
            (List.append (List.replicate 2 none)
              (List.append (List.replicate (2 * scratchCount) none)
                (List.append (List.replicate 2 none) tail)))) =
        List.append (List.replicate (16 + 2 * scratchCount) none)
          tail
    calc
      _ =
          List.append (List.replicate (8 + 4) none)
            (List.append (List.replicate 2 none)
              (List.append (List.replicate (2 * scratchCount) none)
                (List.append (List.replicate 2 none) tail))) := by
            exact
              (FoC.Computability.list_replicate_add_append
                (none : Option Bool) 8 4 _).symm
      _ =
          List.append (List.replicate ((8 + 4) + 2) none)
            (List.append (List.replicate (2 * scratchCount) none)
              (List.append (List.replicate 2 none) tail)) := by
            exact
              (FoC.Computability.list_replicate_add_append
                (none : Option Bool) (8 + 4) 2 _).symm
      _ =
          List.append
            (List.replicate (((8 + 4) + 2) + 2 * scratchCount) none)
            (List.append (List.replicate 2 none) tail) := by
            exact
              (FoC.Computability.list_replicate_add_append
                (none : Option Bool) ((8 + 4) + 2)
                (2 * scratchCount) _).symm
      _ =
          List.append
            (List.replicate
              ((((8 + 4) + 2) + 2 * scratchCount) + 2) none)
            tail := by
            exact
              (FoC.Computability.list_replicate_add_append
                (none : Option Bool)
                (((8 + 4) + 2) + 2 * scratchCount) 2 _).symm
      _ =
          List.append (List.replicate (16 + 2 * scratchCount) none)
            tail := by
            rw [show
              (((8 + 4) + 2) + 2 * scratchCount) + 2 =
                16 + 2 * scratchCount by lia]
  change
    ({ state := knownExitState hit
       tape := tapeAtCells
         (List.append (List.replicate 4 none)
           (List.append
             (MetadataTokenCopy.encodedTokens
               (MetadataWitnessBridge.natTokens q)).reverse
             (List.append (List.replicate 8 none)
               (List.append (List.replicate 4 none)
                 (none :: none ::
                   List.append (List.replicate (2 * scratchCount) none)
                     (none :: none ::
                       List.append
                         (MetadataTokenCopy.encodedTokens raw).reverse
                         (some false :: none :: left)))))))
         (none :: right) } : MachineDescription.Configuration) =
      ({ state := knownExitState hit
         tape := knownTargetTape left raw scratchCount q right } :
        MachineDescription.Configuration)
  rw [hblanks]
  unfold knownTargetTape
  rfl

theorem run_other
    (left : List (Option Bool))
    (raw : List MetadataTokenCopy.TokenKind)
    (scratchCount : Nat) (hit : Bool)
    (right : List (Option Bool)) :
    exists steps : Nat,
      description.runConfig steps
          { state := description.start
            tape := sourceTape left raw scratchCount hit
              (MetadataTokenCopy.encodedTokenCells .zero) right } =
        { state := otherExitState hit
          tape := otherTargetTape left raw scratchCount right } := by
  refine ⟨2 +
      (8 * raw.length +
        (4 +
          (2 * scratchCount +
            (2 +
              (4 +
                (8 + 4)))))), ?_⟩
  unfold sourceTape
  simp only [List.append]
  rw [MachineDescription.runConfig_add]
  rw [run_open]
  rw [MachineDescription.runConfig_add]
  rw [run_raw_tokens]
  rw [MachineDescription.runConfig_add]
  rw [run_raw_delimiter]
  rw [MachineDescription.runConfig_add]
  rw [run_scratch]
  rw [MachineDescription.runConfig_add]
  rw [run_head_marker]
  rw [MachineDescription.runConfig_add]
  rw [run_hit_separator]
  rw [MachineDescription.runConfig_add]
  rw [run_other_tag]
  rw [run_other_final]
  have hblanks (tail : List (Option Bool)) :
      List.append (List.replicate 4 none)
          (List.append (List.replicate 8 none)
            (List.append (List.replicate 4 none)
              (none :: none ::
                List.append (List.replicate (2 * scratchCount) none)
                  (none :: none :: tail)))) =
        List.append (List.replicate (20 + 2 * scratchCount) none)
          tail := by
    change
      List.append (List.replicate 4 none)
          (List.append (List.replicate 8 none)
            (List.append (List.replicate 4 none)
              (List.append (List.replicate 2 none)
                (List.append (List.replicate (2 * scratchCount) none)
                  (List.append (List.replicate 2 none) tail))))) =
        List.append (List.replicate (20 + 2 * scratchCount) none)
          tail
    calc
      _ =
          List.append (List.replicate (4 + 8) none)
            (List.append (List.replicate 4 none)
              (List.append (List.replicate 2 none)
                (List.append (List.replicate (2 * scratchCount) none)
                  (List.append (List.replicate 2 none) tail)))) := by
            exact
              (FoC.Computability.list_replicate_add_append
                (none : Option Bool) 4 8 _).symm
      _ =
          List.append (List.replicate ((4 + 8) + 4) none)
            (List.append (List.replicate 2 none)
              (List.append (List.replicate (2 * scratchCount) none)
                (List.append (List.replicate 2 none) tail))) := by
            exact
              (FoC.Computability.list_replicate_add_append
                (none : Option Bool) (4 + 8) 4 _).symm
      _ =
          List.append (List.replicate (((4 + 8) + 4) + 2) none)
            (List.append (List.replicate (2 * scratchCount) none)
              (List.append (List.replicate 2 none) tail)) := by
            exact
              (FoC.Computability.list_replicate_add_append
                (none : Option Bool) ((4 + 8) + 4) 2 _).symm
      _ =
          List.append
            (List.replicate ((((4 + 8) + 4) + 2) +
              2 * scratchCount) none)
            (List.append (List.replicate 2 none) tail) := by
            exact
              (FoC.Computability.list_replicate_add_append
                (none : Option Bool) (((4 + 8) + 4) + 2)
                (2 * scratchCount) _).symm
      _ =
          List.append
            (List.replicate (((((4 + 8) + 4) + 2) +
              2 * scratchCount) + 2) none)
            tail := by
            exact
              (FoC.Computability.list_replicate_add_append
                (none : Option Bool)
                ((((4 + 8) + 4) + 2) + 2 * scratchCount) 2 _).symm
      _ =
          List.append (List.replicate (20 + 2 * scratchCount) none)
            tail := by
            rw [show
              ((((4 + 8) + 4) + 2) + 2 * scratchCount) + 2 =
                20 + 2 * scratchCount by lia]
  change
    ({ state := otherExitState hit
       tape := tapeAtCells
         (List.append (List.replicate 4 none)
           (List.append (List.replicate 8 none)
             (List.append (List.replicate 4 none)
               (none :: none ::
                 List.append (List.replicate (2 * scratchCount) none)
                   (none :: none ::
                     List.append
                       (MetadataTokenCopy.encodedTokens raw).reverse
                       (some false :: none :: left))))))
         (none :: right) } : MachineDescription.Configuration) =
      ({ state := otherExitState hit
         tape := otherTargetTape left raw scratchCount right } :
        MachineDescription.Configuration)
  rw [hblanks]
  unfold otherTargetTape
  rfl

end GuardedEgress.MetadataWitnessSuffixParser
end FoC.Computability.EncRewriters.BoundedLayoutRunner.RunConfigEmitterCore
