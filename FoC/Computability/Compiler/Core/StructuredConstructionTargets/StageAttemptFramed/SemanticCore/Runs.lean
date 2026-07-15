import FoC.Computability.Compiler.Core.StructuredConstructionTargets.StageAttemptFramed.SemanticCore.Machine
import FoC.Computability.Compiler.Dovetail.Scanner.Basic

namespace FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore

open Languages
open MachineDescription
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape
open EncRewriters.CanonicalLayouts.DovetailLayoutScanner
open DovetailInitialLayoutInitializer.StageInputMarkedScanner

def cfg (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (s : CoreState) (T0 T1 T2 : Tape Bool) : Structured.Configuration :=
  (table attempt hattempt).config s T0 T1 T2

def Leads (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (c d : Structured.Configuration) : Prop :=
  (table attempt hattempt).Leads c d

namespace Leads

theorem refl (attempt : MachineDescription) (hattempt : attempt.SubroutineReady)
    (c : Structured.Configuration) : Leads attempt hattempt c c :=
  TypedStateTable.Leads.refl (table attempt hattempt) c

theorem trans {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady} {c d e : Structured.Configuration}
    (hcd : Leads attempt hattempt c d)
    (hde : Leads attempt hattempt d e) : Leads attempt hattempt c e :=
  TypedStateTable.Leads.trans hcd hde

theorem to_runConfig {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady} {c d : Structured.Configuration}
    (h : Leads attempt hattempt c d) :
    exists j, (coreD attempt hattempt).runConfig j c = d :=
  TypedStateTable.Leads.to_runConfig h

end Leads

theorem leads_step {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady} {s : CoreState}
    (hs : StateBounded attempt s) {T0 T1 T2 : Tape Bool}
    {st : TypedStep CoreState}
    (hnext : next attempt s (Tape.read T0) (Tape.read T1) (Tape.read T2) = some st) :
    Leads attempt hattempt (cfg attempt hattempt s T0 T1 T2)
      (cfg attempt hattempt st.target
        (st.action0.apply T0) (st.action1.apply T1) (st.action2.apply T2)) := by
  simpa [Leads, cfg] using
    TypedStateTable.leads_step (table attempt hattempt)
      (mem_states_of_stateBounded hs) hnext rfl rfl rfl

def cells (bits : Word Bool) : List (Option Bool) := bits.map some

def stageInputBits (C : DovetailControllerLayout) : Word Bool :=
  encodeCodeWordAsInput (PairedRecognizerDovetailControllerStageInputCode C)

def resultBits (w : Word Bool) : Word Bool :=
  encodeCodeWordAsInput (encodeBoolWord w)

def pushWord (bits : Word Bool) (left : List (Option Bool)) :
    List (Option Bool) :=
  List.append (cells bits).reverse left

theorem cells_append (a b : Word Bool) :
    cells (List.append a b) = List.append (cells a) (cells b) := by
  induction a with
  | nil => rfl
  | cons bit rest ih =>
      change some bit :: cells (List.append rest b) =
        some bit :: List.append (cells rest) (cells b)
      rw [ih]

theorem append_nested_assoc (a b c d : List (Option Bool)) :
    List.append (List.append a (List.append b c)) d =
      List.append a (List.append b (List.append c d)) := by
  exact
    (@List.append_assoc (Option Bool) a (List.append b c) d).trans
      (congrArg (fun xs => List.append a xs)
        (@List.append_assoc (Option Bool) b c d))

theorem cellsBits_eq_cellsCodeBits (w : Word Bool) :
    cellsBits w =
      EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits
        (w.map some) := by
  induction w with
  | nil => rfl
  | cons bit rest ih =>
      rw [cellsBits_cons]
      change
        List.append (cellBits bit) (cellsBits rest) =
          List.append
            (EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellCodeBits
              (some bit))
            (EncRewriters.CanonicalLayouts.DovetailLayoutScanner.cellsCodeBits
              (rest.map some))
      rw [ih]
      cases bit <;> rfl

theorem stageInputBits_eq (C : DovetailControllerLayout) :
    stageInputBits C =
      List.append (stageNatBits C.input.length)
        (List.append (cellsBits C.input) (stageNatBits C.stage)) := by
  rw [show stageInputBits C =
      encodeCodeWordAsInput
        (encodeBoolWordAppend C.input (encodeNatAppend C.stage [])) by
    simp [stageInputBits,
      CommonGround.ControllerLayouts.stageInputCode_eq_boolWordNat]]
  rw [boolWordBits_eq_encodeBoolWordAppend C.input
    (encodeNatAppend C.stage ([] : Word MachineCodeSymbol))]
  rw [← cellsBits_eq_cellsCodeBits]
  rw [EncRewriters.CanonicalLayouts.DovetailStagePrefix.natBits_eq_encodeNatAppend]
  simp [encodeCodeWordAsInput]

theorem stageNatBits_succ' (n : Nat) :
    stageNatBits (Nat.succ n) =
      false :: false :: true :: false :: stageNatBits n := by
  simpa only [Nat.succ_eq_add_one] using stageNatBits_succ n

theorem pushWord_append (a b : Word Bool)
    (left : List (Option Bool)) :
    pushWord (List.append a b) left = pushWord b (pushWord a left) := by
  unfold pushWord
  rw [cells_append]
  calc
    List.append (List.reverse (List.append (cells a) (cells b))) left =
        List.append
          (List.append (List.reverse (cells b)) (List.reverse (cells a)))
          left := congrArg (fun xs => List.append xs left)
            (@List.reverse_append (Option Bool) (cells a) (cells b))
    _ = List.append (List.reverse (cells b))
          (List.append (List.reverse (cells a)) left) :=
      List.append_assoc _ _ _

theorem pushWord_cons (bit : Bool) (bits : Word Bool)
    (left : List (Option Bool)) :
    pushWord (bit :: bits) left = pushWord bits (some bit :: left) := by
  simp [pushWord, cells, List.append_assoc]

theorem pushWord_cellBits (bit : Bool)
    (left : List (Option Bool)) :
    pushWord (cellBits bit) left =
      some (!bit) :: some bit :: some true :: some false :: left := by
  cases bit <;> rfl

theorem cells_cellBits (bit : Bool) :
    cells (cellBits bit) =
      [some false, some true, some bit, some (!bit)] := by
  cases bit <;> rfl

theorem controllerBits_eq (C : DovetailControllerLayout) :
    StructuredConstructionTargets.stageAttemptFramedStructuredInputBits C =
      List.append [false, false, false, false]
        (List.append (stageInputBits C) (resultBits C.result)) := by
  unfold StructuredConstructionTargets.stageAttemptFramedStructuredInputBits
  rw [CommonGround.ControllerLayouts.encode_eq_header_stageInput_append_result]
  change
    List.append [false, false, false, false]
        (encodeCodeWordAsInput
          (List.append (PairedRecognizerDovetailControllerStageInputCode C)
            (encodeBoolWordAppend C.result []))) = _
  rw [encodeCodeWordAsInput_append]
  rfl

theorem outputBits_eq (C : DovetailControllerLayout) (result : Word Bool) :
    encodeCodeWordAsInput
        (DovetailControllerLayout.encode
          (DovetailControllerLayout.withResult C result)) =
      List.append [false, false, false, false]
        (List.append (stageInputBits C) (resultBits result)) := by
  rw [CommonGround.ControllerLayouts.withResult_encode_eq_stageInput_append_result]
  change
    List.append [false, false, false, false]
        (encodeCodeWordAsInput
          (List.append (PairedRecognizerDovetailControllerStageInputCode C)
            (encodeBoolWordAppend result []))) = _
  rw [encodeCodeWordAsInput_append]
  rfl

theorem leads_copy_both {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady} {s target : CoreState}
    (hs : StateBounded attempt s) (bit : Bool)
    (hnext : forall r1 r2,
      next attempt s (some bit) r1 r2 = some (copyBoth target bit))
    (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt s
        (tapeAtCells L0 (some bit :: tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt target
        (tapeAtCells (some bit :: L0) tail)
        (tapeAtCells (some bit :: L1) [])
        (tapeAtCells (some bit :: L2) [])) := by
  have h := leads_step (attempt := attempt) (hattempt := hattempt)
    (s := s) hs
    (T0 := tapeAtCells L0 (some bit :: tail))
    (T1 := tapeAtCells L1 []) (T2 := tapeAtCells L2 [])
    (st := copyBoth target bit) (by
      change next attempt s (some bit) none none = _
      exact hnext none none)
  change
    Leads attempt hattempt _
      (cfg attempt hattempt target
        (keepR.apply (tapeAtCells L0 (some bit :: tail)))
        ((writeR (some bit)).apply (tapeAtCells L1 []))
        ((writeR (some bit)).apply (tapeAtCells L2 []))) at h
  have h0 : keepR.apply (tapeAtCells L0 (some bit :: tail)) =
      tapeAtCells (some bit :: L0) tail := by cases tail <;> rfl
  rw [h0] at h
  exact h

theorem leads_copy_marker {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady} {s target : CoreState}
    (hs : StateBounded attempt s)
    (hnext : forall r1 r2, next attempt s (some false) r1 r2 =
      some (copyOutput target true))
    (L0 L2 tail : List (Option Bool)) (T1 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt s
        (tapeAtCells L0 (some false :: tail)) T1 (tapeAtCells L2 []))
      (cfg attempt hattempt target
        (tapeAtCells (some false :: L0) tail) T1
        (tapeAtCells (some true :: L2) [])) := by
  have h := leads_step (attempt := attempt) (hattempt := hattempt)
    (s := s) hs
    (T0 := tapeAtCells L0 (some false :: tail))
    (T1 := T1) (T2 := tapeAtCells L2 [])
    (st := copyOutput target true) (by
      change next attempt s (some false) (Tape.read T1) none = _
      exact hnext (Tape.read T1) none)
  change
    Leads attempt hattempt _
      (cfg attempt hattempt target
        (keepR.apply (tapeAtCells L0 (some false :: tail))) T1
        ((writeR (some true)).apply (tapeAtCells L2 []))) at h
  have h0 : keepR.apply (tapeAtCells L0 (some false :: tail)) =
      tapeAtCells (some false :: L0) tail := by cases tail <;> rfl
  rw [h0] at h
  exact h

theorem leads_copy_four {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    {s0 s1 s2 s3 s4 : CoreState} (b0 b1 b2 b3 : Bool)
    (h0 : forall r1 r2,
      next attempt s0 (some b0) r1 r2 = some (copyBoth s1 b0))
    (h1 : forall r1 r2,
      next attempt s1 (some b1) r1 r2 = some (copyBoth s2 b1))
    (h2 : forall r1 r2,
      next attempt s2 (some b2) r1 r2 = some (copyBoth s3 b2))
    (h3 : forall r1 r2,
      next attempt s3 (some b3) r1 r2 = some (copyBoth s4 b3))
    (hs0 : StateBounded attempt s0) (hs1 : StateBounded attempt s1)
    (hs2 : StateBounded attempt s2) (hs3 : StateBounded attempt s3)
    (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt s0
        (tapeAtCells L0
          (some b0 :: some b1 :: some b2 :: some b3 :: tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt s4
        (tapeAtCells (some b3 :: some b2 :: some b1 :: some b0 :: L0) tail)
        (tapeAtCells (some b3 :: some b2 :: some b1 :: some b0 :: L1) [])
        (tapeAtCells (some b3 :: some b2 :: some b1 :: some b0 :: L2) [])) := by
  refine (leads_copy_both (attempt := attempt) (hattempt := hattempt)
    (s := s0) (target := s1) hs0 b0 h0 L0 L1 L2 _).trans ?_
  refine (leads_copy_both (attempt := attempt) (hattempt := hattempt)
    (s := s1) (target := s2) hs1 b1 h1 _ _ _ _).trans ?_
  refine (leads_copy_both (attempt := attempt) (hattempt := hattempt)
    (s := s2) (target := s3) hs2 b2 h2 _ _ _ _).trans ?_
  exact leads_copy_both (attempt := attempt) (hattempt := hattempt)
    (s := s3) (target := s4) hs3 b3 h3 _ _ _ tail

theorem leads_header {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (L0 L2 : List (Option Bool)) (tail : List (Option Bool))
    (T1 : Tape Bool) :
    Leads attempt hattempt
      (cfg attempt hattempt .header0
        (tapeAtCells L0
          (some false :: some false :: some false :: some false :: tail))
        T1 (tapeAtCells L2 []))
      (cfg attempt hattempt .inputLen0
        (tapeAtCells
          (some false :: some false :: some false :: some false :: L0) tail)
        T1
        (tapeAtCells
          (some true :: some true :: some true :: some true :: L2) [])) := by
  refine (leads_copy_marker (attempt := attempt) (hattempt := hattempt)
    (s := .header0) (target := .header1) trivial (fun _ _ => rfl)
    L0 L2 _ T1).trans ?_
  refine (leads_copy_marker (attempt := attempt) (hattempt := hattempt)
    (s := .header1) (target := .header2) trivial (fun _ _ => rfl)
    _ _ _ T1).trans ?_
  refine (leads_copy_marker (attempt := attempt) (hattempt := hattempt)
    (s := .header2) (target := .header3) trivial (fun _ _ => rfl)
    _ _ _ T1).trans ?_
  exact leads_copy_marker (attempt := attempt) (hattempt := hattempt)
    (s := .header3) (target := .inputLen0) trivial (fun _ _ => rfl)
    _ _ tail T1

theorem leads_inputLength_tick {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .inputLen0
        (tapeAtCells L0
          (some false :: some false :: some true :: some false :: tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt .inputLen0
        (tapeAtCells (some false :: some true :: some false :: some false :: L0) tail)
        (tapeAtCells (some false :: some true :: some false :: some false :: L1) [])
        (tapeAtCells (some false :: some true :: some false :: some false :: L2) [])) :=
  leads_copy_four (s0 := .inputLen0) (s1 := .inputLen1)
    (s2 := .inputLen2) (s3 := .inputLen3) (s4 := .inputLen0)
    false false true false
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    trivial trivial trivial trivial
    L0 L1 L2 tail

theorem leads_inputLength_done {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .inputLen0
        (tapeAtCells L0
          (some false :: some false :: some true :: some true :: tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt .field0
        (tapeAtCells (some true :: some true :: some false :: some false :: L0) tail)
        (tapeAtCells (some true :: some true :: some false :: some false :: L1) [])
        (tapeAtCells (some true :: some true :: some false :: some false :: L2) [])) :=
  leads_copy_four (s0 := .inputLen0) (s1 := .inputLen1)
    (s2 := .inputLen2) (s3 := .inputLen3) (s4 := .field0)
    false false true true
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    trivial trivial trivial trivial
    L0 L1 L2 tail

theorem leads_inputCell {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (bit : Bool) (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .field0
        (tapeAtCells L0
          (some false :: some true :: some bit :: some (!bit) :: tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt .field0
        (tapeAtCells (some (!bit) :: some bit :: some true :: some false :: L0) tail)
        (tapeAtCells (some (!bit) :: some bit :: some true :: some false :: L1) [])
        (tapeAtCells (some (!bit) :: some bit :: some true :: some false :: L2) [])) := by
  cases bit
  · exact leads_copy_four (s0 := .field0) (s1 := .field1)
      (s2 := .cell2) (s3 := .cell3 false) (s4 := .field0)
      _ _ _ _
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      trivial trivial trivial trivial L0 L1 L2 tail
  · exact leads_copy_four (s0 := .field0) (s1 := .field1)
      (s2 := .cell2) (s3 := .cell3 true) (s4 := .field0)
      _ _ _ _
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      trivial trivial trivial trivial L0 L1 L2 tail

theorem leads_firstStageToken {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (done : Bool) (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .field0
        (tapeAtCells L0
          (some false :: some false :: some true :: some done :: tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt (if done then .eraseRight else .stage0)
        (tapeAtCells (some done :: some true :: some false :: some false :: L0) tail)
        (tapeAtCells (some done :: some true :: some false :: some false :: L1) [])
        (tapeAtCells (some done :: some true :: some false :: some false :: L2) [])) := by
  cases done
  · exact leads_copy_four (s0 := .field0) (s1 := .field1)
      (s2 := .stage2) (s3 := .stage3) (s4 := .stage0)
      _ _ _ _
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      trivial trivial trivial trivial L0 L1 L2 tail
  · exact leads_copy_four (s0 := .field0) (s1 := .field1)
      (s2 := .stage2) (s3 := .stage3) (s4 := .eraseRight)
      _ _ _ _
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      trivial trivial trivial trivial L0 L1 L2 tail

theorem leads_stageToken {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (done : Bool) (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .stage0
        (tapeAtCells L0
          (some false :: some false :: some true :: some done :: tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt (if done then .eraseRight else .stage0)
        (tapeAtCells (some done :: some true :: some false :: some false :: L0) tail)
        (tapeAtCells (some done :: some true :: some false :: some false :: L1) [])
        (tapeAtCells (some done :: some true :: some false :: some false :: L2) [])) := by
  cases done
  · exact leads_copy_four (s0 := .stage0) (s1 := .stage1)
      (s2 := .stage2) (s3 := .stage3) (s4 := .stage0)
      _ _ _ _
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      trivial trivial trivial trivial L0 L1 L2 tail
  · exact leads_copy_four (s0 := .stage0) (s1 := .stage1)
      (s2 := .stage2) (s3 := .stage3) (s4 := .eraseRight)
      _ _ _ _
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      trivial trivial trivial trivial L0 L1 L2 tail

theorem leads_inputLength {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (n : Nat) (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .inputLen0
        (tapeAtCells L0
          (List.append (cells (stageNatBits n)) tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt .field0
        (tapeAtCells (pushWord (stageNatBits n) L0) tail)
        (tapeAtCells (pushWord (stageNatBits n) L1) [])
        (tapeAtCells (pushWord (stageNatBits n) L2) [])) := by
  induction n generalizing L0 L1 L2 with
  | zero =>
      simpa [stageNatBits_zero, pushWord, cells] using
        (leads_inputLength_done (attempt := attempt) (hattempt := hattempt)
          L0 L1 L2 tail)
  | succ n ih =>
      rw [stageNatBits_succ']
      refine (leads_inputLength_tick (attempt := attempt)
        (hattempt := hattempt) L0 L1 L2 _).trans ?_
      simpa only [cells, List.map_cons, List.append_cons, pushWord_cons] using
        (ih
          (some false :: some true :: some false :: some false :: L0)
          (some false :: some true :: some false :: some false :: L1)
          (some false :: some true :: some false :: some false :: L2))

theorem leads_inputCells {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (w : Word Bool) (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .field0
        (tapeAtCells L0 (List.append (cells (cellsBits w)) tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt .field0
        (tapeAtCells (pushWord (cellsBits w) L0) tail)
        (tapeAtCells (pushWord (cellsBits w) L1) [])
        (tapeAtCells (pushWord (cellsBits w) L2) [])) := by
  induction w generalizing L0 L1 L2 with
  | nil => exact Leads.refl _ _ _
  | cons bit rest ih =>
      rw [cellsBits_cons, cells_append]
      have hassoc :
          List.append
              (List.append (cells (cellBits bit)) (cells (cellsBits rest)))
              tail =
            List.append (cells (cellBits bit))
              (List.append (cells (cellsBits rest)) tail) :=
        List.append_assoc _ _ _
      rw [hassoc]
      rw [cells_cellBits]
      refine (leads_inputCell (attempt := attempt) (hattempt := hattempt)
        bit L0 L1 L2 (List.append (cells (cellsBits rest)) tail)).trans ?_
      simpa only [pushWord_append, pushWord_cellBits] using
        (ih
          (some (!bit) :: some bit :: some true :: some false :: L0)
          (some (!bit) :: some bit :: some true :: some false :: L1)
          (some (!bit) :: some bit :: some true :: some false :: L2))

theorem leads_stageRest {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (n : Nat) (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .stage0
        (tapeAtCells L0 (List.append (cells (stageNatBits n)) tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt .eraseRight
        (tapeAtCells (pushWord (stageNatBits n) L0) tail)
        (tapeAtCells (pushWord (stageNatBits n) L1) [])
        (tapeAtCells (pushWord (stageNatBits n) L2) [])) := by
  induction n generalizing L0 L1 L2 with
  | zero =>
      simpa [stageNatBits_zero, pushWord, cells] using
        (leads_stageToken (attempt := attempt) (hattempt := hattempt)
          true L0 L1 L2 tail)
  | succ n ih =>
      rw [stageNatBits_succ']
      refine (leads_stageToken (attempt := attempt) (hattempt := hattempt)
        false L0 L1 L2 _).trans ?_
      simpa only [cells, List.map_cons, List.append_cons, pushWord_cons,
        Bool.false_eq_true, if_false] using
        (ih
          (some false :: some true :: some false :: some false :: L0)
          (some false :: some true :: some false :: some false :: L1)
          (some false :: some true :: some false :: some false :: L2))

theorem leads_stageNumber {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady}
    (n : Nat) (L0 L1 L2 tail : List (Option Bool)) :
    Leads attempt hattempt
      (cfg attempt hattempt .field0
        (tapeAtCells L0 (List.append (cells (stageNatBits n)) tail))
        (tapeAtCells L1 []) (tapeAtCells L2 []))
      (cfg attempt hattempt .eraseRight
        (tapeAtCells (pushWord (stageNatBits n) L0) tail)
        (tapeAtCells (pushWord (stageNatBits n) L1) [])
        (tapeAtCells (pushWord (stageNatBits n) L2) [])) := by
  cases n with
  | zero =>
      simpa [stageNatBits_zero, pushWord, cells] using
        (leads_firstStageToken (attempt := attempt) (hattempt := hattempt)
          true L0 L1 L2 tail)
  | succ n =>
      rw [stageNatBits_succ']
      refine (leads_firstStageToken (attempt := attempt) (hattempt := hattempt)
        false L0 L1 L2 _).trans ?_
      simpa only [cells, List.map_cons, List.append_cons, pushWord_cons,
        Bool.false_eq_true, if_false] using
        (leads_stageRest (attempt := attempt) (hattempt := hattempt)
          n
          (some false :: some true :: some false :: some false :: L0)
          (some false :: some true :: some false :: some false :: L1)
          (some false :: some true :: some false :: some false :: L2)
          tail)

def parsedInputLeft0 (C : DovetailControllerLayout) :
    List (Option Bool) :=
  pushWord (stageNatBits C.stage)
    (pushWord (cellsBits C.input)
      (pushWord (stageNatBits C.input.length)
        [some false, some false, some false, some false]))

def parsedInputLeft1 (C : DovetailControllerLayout) :
    List (Option Bool) :=
  pushWord (stageNatBits C.stage)
    (pushWord (cellsBits C.input)
      (pushWord (stageNatBits C.input.length) []))

def parsedInputLeft2 (C : DovetailControllerLayout) :
    List (Option Bool) :=
  pushWord (stageNatBits C.stage)
    (pushWord (cellsBits C.input)
      (pushWord (stageNatBits C.input.length)
        [some true, some true, some true, some true]))

theorem leads_parse_controller {attempt : MachineDescription}
    {hattempt : attempt.SubroutineReady} (C : DovetailControllerLayout) :
    Leads attempt hattempt
      (cfg attempt hattempt .header0
        (Tape.input
          (StructuredConstructionTargets.stageAttemptFramedStructuredInputBits C))
        Tape.blank Tape.blank)
      (cfg attempt hattempt .eraseRight
        (tapeAtCells (parsedInputLeft0 C) (cells (resultBits C.result)))
        (tapeAtCells (parsedInputLeft1 C) [])
        (tapeAtCells (parsedInputLeft2 C) [])) := by
  rw [controllerBits_eq]
  change Leads attempt hattempt
    (cfg attempt hattempt .header0
      (tapeAtCells []
        (some false :: some false :: some false :: some false ::
          cells (List.append (stageInputBits C) (resultBits C.result))))
      (tapeAtCells [] []) (tapeAtCells [] [])) _
  rw [cells_append, stageInputBits_eq, cells_append, cells_append]
  rw [append_nested_assoc]
  refine (leads_header (attempt := attempt) (hattempt := hattempt)
    [] [] _ (tapeAtCells [] [])).trans ?_
  refine (leads_inputLength (attempt := attempt) (hattempt := hattempt)
    C.input.length _ _ _ _).trans ?_
  refine (leads_inputCells (attempt := attempt) (hattempt := hattempt)
    C.input _ _ _ _).trans ?_
  simpa [parsedInputLeft0, parsedInputLeft1, parsedInputLeft2] using
    (leads_stageNumber (attempt := attempt) (hattempt := hattempt)
      C.stage _ _ _ (cells (resultBits C.result)))
end FoC.Computability.StructuredConstructionTargets.StageAttemptFramed.SemanticCore
