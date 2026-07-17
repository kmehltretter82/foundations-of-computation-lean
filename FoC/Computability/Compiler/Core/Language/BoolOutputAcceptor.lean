import FoC.Computability.Compiler.Core.Language
import FoC.Computability.Compiler.Core.TransitionTableChecks
import FoC.Computability.Compiler.SeqSubroutineSemantics
import FoC.Computability.TransformPart2

set_option doc.verso true

/-!
# Finite Boolean-output acceptors

This target-local construction turns one normalized Boolean output of a
halt-stable finite decider into ordinary halting.  Its scanner starts at an
arbitrary head position, uses the other Boolean as a temporary marker, and
alternates finite sweeps until it observes the requested Boolean.
-/

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace BoolOutputAcceptor

/-!
## Arbitrary-head Boolean-presence scanner
-/

def FixedBoolPresenceScannerDescription (b : Bool) : MachineDescription where
  stateCount := 4
  start := 0
  halt := 3
  transitions :=
    [ transition 0 (some b) (some b) Direction.right 3
    , transition 0 (some (!b)) (some (!b)) Direction.right 1
    , transition 0 none (some (!b)) Direction.right 1
    , transition 1 (some b) (some b) Direction.right 3
    , transition 1 (some (!b)) (some (!b)) Direction.right 1
    , transition 1 none (some (!b)) Direction.left 2
    , transition 2 (some b) (some b) Direction.right 3
    , transition 2 (some (!b)) (some (!b)) Direction.left 2
    , transition 2 none (some (!b)) Direction.right 1 ]

theorem fixedBoolPresenceScanner_subroutineReady (b : Bool) :
    (FixedBoolPresenceScannerDescription b).SubroutineReady := by
  apply machineDescription_subroutineReady_of_transition_checks
  all_goals cases b <;> decide

private def scannerBaseMachine : TuringMachine Bool Unit where
  start := ()
  halt := ()
  transition := fun _ _ => none
  statesFinite := Foundation.FiniteType.unit

private def scannerStateCode :
    NormalizedDeciderToAcceptorState Unit -> Nat
  | NormalizedDeciderToAcceptorState.run _ => 0
  | NormalizedDeciderToAcceptorState.sweepRight => 1
  | NormalizedDeciderToAcceptorState.sweepLeft => 2
  | NormalizedDeciderToAcceptorState.accept => 3

private def scannerConfigCode
    (c : TuringMachine.Configuration Bool
      (NormalizedDeciderToAcceptorState Unit)) :
    MachineDescription.Configuration where
  state := scannerStateCode c.state
  tape := c.tape

private theorem fixedBoolPresenceScanner_stepConfig_of_semanticStep
    (b : Bool)
    {c d : TuringMachine.Configuration Bool
      (NormalizedDeciderToAcceptorState Unit)}
    (hstep : TuringMachine.Step
      (TuringMachine.normalizedDeciderToAcceptor scannerBaseMachine (!b) b)
      c d) :
    (FixedBoolPresenceScannerDescription b).stepConfig
        (scannerConfigCode c) =
      some (scannerConfigCode d) := by
  rw [TuringMachine.step_iff_transition_eq_some] at hstep
  rcases hstep with ⟨write, dir, nextState, htransition, rfl⟩
  rcases c with ⟨state, tape⟩
  cases b <;> cases state
  all_goals
    cases hread : Tape.read tape
    · simp [TuringMachine.normalizedDeciderToAcceptor,
        TuringMachine.normalizedDeciderToAcceptorTransition,
        scannerBaseMachine, hread] at htransition
      all_goals
        rcases htransition with ⟨hwrite, hdir, hstate⟩
        subst write
        subst dir
        subst nextState
        simp [FixedBoolPresenceScannerDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches,
          transition, scannerConfigCode, scannerStateCode, hread]
    · rename_i bit
      cases bit <;>
        simp [TuringMachine.normalizedDeciderToAcceptor,
          TuringMachine.normalizedDeciderToAcceptorTransition,
          scannerBaseMachine, hread] at htransition
      all_goals
        rcases htransition with ⟨hwrite, hdir, hstate⟩
        subst write
        subst dir
        subst nextState
        simp [FixedBoolPresenceScannerDescription,
          MachineDescription.stepConfig,
          MachineDescription.lookupTransition, MachineDescription.Matches, transition,
          scannerConfigCode, scannerStateCode, hread]

private theorem fixedBoolPresenceScanner_runConfig_of_computesIn
    (b : Bool)
    {n : Nat}
    {c d : TuringMachine.Configuration Bool
      (NormalizedDeciderToAcceptorState Unit)}
    (hcomp : TuringMachine.ComputesIn
      (TuringMachine.normalizedDeciderToAcceptor scannerBaseMachine (!b) b)
      n c d) :
    (FixedBoolPresenceScannerDescription b).runConfig n
        (scannerConfigCode c) =
      scannerConfigCode d := by
  induction hcomp with
  | zero c => rfl
  | succ hstep _ ih =>
      simp [MachineDescription.runConfig,
        fixedBoolPresenceScanner_stepConfig_of_semanticStep b hstep, ih]

theorem fixedBoolPresenceScanner_halts_of_normalizedOutput
    (b : Bool) {Tin : Tape Bool}
    (hout : Tape.normalizedOutput Tin = [b]) :
    exists Tout : Tape Bool,
      (FixedBoolPresenceScannerDescription b).HaltsFromTape Tin Tout := by
  let source : TuringMachine.Configuration Bool Unit :=
    { state := (), tape := Tin }
  have hsemantic :
      TuringMachine.HaltsFrom
        (TuringMachine.normalizedDeciderToAcceptor scannerBaseMachine (!b) b)
        (TuringMachine.normalizedRunConfig source) :=
    TuringMachine.normalizedOutputScannerComplete scannerBaseMachine
      (by cases b <;> decide) source
      (by simp [source, TuringMachine.Halted, scannerBaseMachine]) hout
  rcases hsemantic with ⟨final, hcomp, hhalt⟩
  rcases TuringMachine.computes_to_computesIn hcomp with ⟨n, hcompIn⟩
  have hrun := fixedBoolPresenceScanner_runConfig_of_computesIn b hcompIn
  refine ⟨final.tape, n, ?_⟩
  dsimp [MachineDescription.HaltsFromTapeIn]
  have hstart :
      scannerConfigCode (TuringMachine.normalizedRunConfig source) =
        { state := (FixedBoolPresenceScannerDescription b).start,
          tape := Tin } := by
    simp [source, scannerConfigCode, scannerStateCode,
      TuringMachine.normalizedRunConfig, FixedBoolPresenceScannerDescription]
  have hfinal :
      scannerConfigCode final =
        { state := (FixedBoolPresenceScannerDescription b).halt,
          tape := final.tape } := by
    rcases final with ⟨state, tape⟩
    change state = NormalizedDeciderToAcceptorState.accept at hhalt
    subst state
    rfl
  rw [← hstart, hrun, hfinal]
  exact ⟨rfl, rfl⟩

private theorem tape_read_ne_some_of_not_mem_normalizedOutput
    (b : Bool) {T : Tape Bool}
    (habsent : ¬ List.Mem b (Tape.normalizedOutput T)) :
    Tape.read T ≠ some b := by
  rcases T with ⟨left, head, right⟩
  intro hread
  change head = some b at hread
  subst head
  apply habsent
  have hmem :
      List.Mem b
        ((List.filterMap (fun cell => cell) left).reverse ++
          b :: List.filterMap (fun cell => cell) right) :=
    List.mem_append.mpr
      (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  simpa [Tape.normalizedOutput, Tape.cells] using hmem

private theorem tape_not_mem_normalizedOutput_write_other
    (b : Bool) {T : Tape Bool}
    (habsent : ¬ List.Mem b (Tape.normalizedOutput T)) :
    ¬ List.Mem b
      (Tape.normalizedOutput (Tape.write (some (!b)) T)) := by
  rcases T with ⟨left, head, right⟩
  intro hnew
  apply habsent
  have hnew' :
      List.Mem b
        ((List.filterMap (fun cell => cell) left).reverse ++
          (!b) :: List.filterMap (fun cell => cell) right) := by
    simpa [Tape.normalizedOutput, Tape.cells, Tape.write,
      List.filterMap_cons] using hnew
  rcases List.mem_append.mp hnew' with hleft | hright
  · have hold :
        List.Mem b
          ((List.filterMap (fun cell => cell) left).reverse ++
            List.filterMap (fun cell => cell) (head :: right)) :=
      List.mem_append.mpr (Or.inl hleft)
    simpa [Tape.normalizedOutput, Tape.cells] using hold
  · rcases List.mem_cons.mp hright with hother | hright
    · have hne : b ≠ !b := by cases b <;> decide
      exact False.elim (hne hother)
    · have htail :
          List.Mem b (List.filterMap (fun cell => cell) (head :: right)) := by
        cases head with
        | none => exact hright
        | some bit => exact List.mem_cons.mpr (Or.inr hright)
      have hold :
          List.Mem b
            ((List.filterMap (fun cell => cell) left).reverse ++
              List.filterMap (fun cell => cell) (head :: right)) :=
        List.mem_append.mpr (Or.inr htail)
      simpa [Tape.normalizedOutput, Tape.cells] using hold

private theorem tape_not_mem_normalizedOutput_move_write_other
    (b : Bool) (dir : Direction) {T : Tape Bool}
    (habsent : ¬ List.Mem b (Tape.normalizedOutput T)) :
    ¬ List.Mem b (Tape.normalizedOutput
      (Tape.move dir (Tape.write (some (!b)) T))) := by
  rw [Tape.normalizedOutput_move]
  exact tape_not_mem_normalizedOutput_write_other b habsent

private theorem fixedBoolPresenceScanner_transition_property
    (b : Bool) {t : TransitionDescription}
    (ht : t ∈ (FixedBoolPresenceScannerDescription b).transitions) :
    (t.target = (FixedBoolPresenceScannerDescription b).halt ->
        t.read = some b) ∧
      (t.target ≠ (FixedBoolPresenceScannerDescription b).halt ->
        t.write = some (!b)) := by
  cases b <;>
    simp [FixedBoolPresenceScannerDescription, transition] at ht ⊢
  all_goals
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

private theorem fixedBoolPresenceScanner_stepConfig_preserves_absence
    (b : Bool) {c d : MachineDescription.Configuration}
    (habsent : ¬ List.Mem b (Tape.normalizedOutput c.tape))
    (hstep : (FixedBoolPresenceScannerDescription b).stepConfig c = some d) :
    ¬ List.Mem b (Tape.normalizedOutput d.tape) ∧
      d.state ≠ (FixedBoolPresenceScannerDescription b).halt := by
  unfold MachineDescription.stepConfig at hstep
  cases hlookup :
      (FixedBoolPresenceScannerDescription b).lookupTransition
        c.state (Tape.read c.tape) with
  | none =>
      rw [hlookup] at hstep
      cases hstep
  | some t =>
      rw [hlookup] at hstep
      cases hstep
      have htmem := MachineDescription.lookupTransition_mem hlookup
      have hmatches := MachineDescription.lookupTransition_matches hlookup
      have hproperty :=
        fixedBoolPresenceScanner_transition_property b htmem
      have hreadNe :=
        tape_read_ne_some_of_not_mem_normalizedOutput b habsent
      constructor
      · by_cases htarget :
            t.target = (FixedBoolPresenceScannerDescription b).halt
        · have hread : Tape.read c.tape = some b :=
            hmatches.right.symm.trans (hproperty.left htarget)
          exact False.elim (hreadNe hread)
        · have hwrite := hproperty.right htarget
          simpa [hwrite] using
            tape_not_mem_normalizedOutput_move_write_other
              b t.move habsent
      · intro htarget
        have hread : Tape.read c.tape = some b :=
          hmatches.right.symm.trans (hproperty.left htarget)
        exact hreadNe hread

private theorem fixedBoolPresenceScanner_runConfig_preserves_absence
    (b : Bool) (n : Nat) {c : MachineDescription.Configuration}
    (habsent : ¬ List.Mem b (Tape.normalizedOutput c.tape))
    (hstate : c.state ≠ (FixedBoolPresenceScannerDescription b).halt) :
    ¬ List.Mem b (Tape.normalizedOutput
        ((FixedBoolPresenceScannerDescription b).runConfig n c).tape) ∧
      ((FixedBoolPresenceScannerDescription b).runConfig n c).state ≠
        (FixedBoolPresenceScannerDescription b).halt := by
  induction n generalizing c with
  | zero => exact ⟨habsent, hstate⟩
  | succ n ih =>
      cases hstep :
          (FixedBoolPresenceScannerDescription b).stepConfig c with
      | none =>
          simpa [MachineDescription.runConfig, hstep] using
            And.intro habsent hstate
      | some next =>
          have hnext :=
            fixedBoolPresenceScanner_stepConfig_preserves_absence
              b habsent hstep
          simpa [MachineDescription.runConfig, hstep] using
            ih hnext.left hnext.right

theorem fixedBoolPresenceScanner_mem_normalizedOutput_of_halts
    (b : Bool) {Tin Tout : Tape Bool}
    (hhalt :
      (FixedBoolPresenceScannerDescription b).HaltsFromTape Tin Tout) :
    List.Mem b (Tape.normalizedOutput Tin) := by
  by_cases hmem : List.Mem b (Tape.normalizedOutput Tin)
  · exact hmem
  · rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape hhalt with
      ⟨n, hrun⟩
    have hinvariant :=
      fixedBoolPresenceScanner_runConfig_preserves_absence b n
        (c :=
          { state := (FixedBoolPresenceScannerDescription b).start,
            tape := Tin }) hmem
        (by simp [FixedBoolPresenceScannerDescription])
    exact False.elim (hinvariant.right (by rw [hrun]))

/-!
## Composition with a finite Boolean-output source
-/

def BoolOutputAcceptorDescription
    (source : MachineDescription) (b : Bool) : MachineDescription :=
  seqSubroutine source (FixedBoolPresenceScannerDescription b) Direction.right

theorem boolOutputAcceptorDescription_subroutineReady
    {source : MachineDescription} (hsource : source.SubroutineReady)
    (b : Bool) :
    (BoolOutputAcceptorDescription source b).SubroutineReady := by
  exact MachineDescription.seqSubroutine_subroutineReady hsource
    (fixedBoolPresenceScanner_subroutineReady b)

private theorem haltsWithOutput_exists_haltsWithTape
    {D : MachineDescription} {w out : Word Bool}
    (hhalt : D.HaltsWithOutput w out) :
    exists T : Tape Bool,
      D.HaltsWithTape w T ∧ Tape.normalizedOutput T = out := by
  rcases hhalt with ⟨n, hn⟩
  let T := (D.runConfig n (D.initial w)).tape
  refine ⟨T, ⟨n, ?_⟩, ?_⟩
  · exact ⟨hn.left, rfl⟩
  · exact hn.right

private theorem haltsWithTape_haltsOnInput
    {D : MachineDescription} {w : Word Bool} {T : Tape Bool}
    (hhalt : D.HaltsWithTape w T) : D.HaltsOnInput w := by
  rcases hhalt with ⟨n, hn⟩
  exact ⟨n, hn.left⟩

private theorem haltsOnInput_exists_haltsWithTape
    {D : MachineDescription} {w : Word Bool}
    (hhalt : D.HaltsOnInput w) :
    exists T : Tape Bool, D.HaltsWithTape w T := by
  rcases hhalt with ⟨n, hn⟩
  let T := (D.runConfig n (D.initial w)).tape
  exact ⟨T, n, hn, rfl⟩

/-- Pointwise output-acceptor characterization: coherence is required only at the fixed input, so a source controlled on canonical encoded inputs still yields a recognizer there. Shared by the Boolean-language and code-language consumers. -/
theorem boolOutputAcceptorDescription_haltsOnInput_iff_pointwise
    {source : MachineDescription} (hsource : source.SubroutineReady)
    (b : Bool) (w : Word Bool)
    (hcoherent :
      forall {T : Tape Bool},
        source.HaltsWithTape w T ->
          List.Mem b (Tape.normalizedOutput T) ->
            Tape.normalizedOutput T = [b]) :
    (BoolOutputAcceptorDescription source b).HaltsOnInput w <->
      source.HaltsWithOutput w [b] := by
  have hscanner := fixedBoolPresenceScanner_subroutineReady b
  constructor
  · intro hhalt
    rcases haltsOnInput_exists_haltsWithTape hhalt with ⟨Tout, hseqTape⟩
    rcases MachineDescription.seqSubroutine_haltsWithTape_inv
        hsource hscanner hseqTape with
      ⟨Tmid, hsourceTape, nB, hBRun⟩
    have hscannerHalt :
        (FixedBoolPresenceScannerDescription b).HaltsFromTape
          (Tape.move Direction.right Tmid) Tout := by
      refine ⟨nB, ?_⟩
      constructor
      · simpa [MachineDescription.HaltsFromTapeIn] using
          congrArg MachineDescription.Configuration.state hBRun
      · simpa [MachineDescription.HaltsFromTapeIn] using
          congrArg MachineDescription.Configuration.tape hBRun
    have hmoved :=
      fixedBoolPresenceScanner_mem_normalizedOutput_of_halts
        b hscannerHalt
    have hmem : List.Mem b (Tape.normalizedOutput Tmid) := by
      rw [Tape.normalizedOutput_move] at hmoved
      exact hmoved
    have hout := hcoherent hsourceTape hmem
    have hsourceOutput :=
      MachineDescription.haltsWithOutput_of_haltsWithTape hsourceTape
    simpa [hout] using hsourceOutput
  · intro hhalt
    rcases haltsWithOutput_exists_haltsWithTape hhalt with
      ⟨Tmid, hsourceTape, hout⟩
    have hmoved :
        Tape.normalizedOutput (Tape.move Direction.right Tmid) = [b] := by
      simpa [Tape.normalizedOutput_move] using hout
    rcases fixedBoolPresenceScanner_halts_of_normalizedOutput b hmoved with
      ⟨Tout, hscannerHalt⟩
    rcases MachineDescription.runConfig_eq_halt_of_haltsFromTape
        hscannerHalt with ⟨nB, hBRun⟩
    have hseqTape :=
      MachineDescription.seqSubroutine_haltsWithTape_of_haltsWithTape
        hsource hscanner hsourceTape ⟨nB, hBRun⟩
    exact haltsWithTape_haltsOnInput hseqTape

theorem stoppedBoolOutputAcceptorConstruction
    (D : MachineDescription) (L : Language Bool)
    (hD : StoppedMachineDescriptionDecidesLanguage D L)
    (b : Bool) :
    exists acceptor : MachineDescription,
      acceptor.SubroutineReady ∧
        forall w : Word Bool,
          acceptor.HaltsOnInput w <-> D.HaltsWithOutput w [b] := by
  have hsource : D.SubroutineReady := ⟨hD.right.left, hD.left⟩
  refine ⟨BoolOutputAcceptorDescription D b,
    boolOutputAcceptorDescription_subroutineReady hsource b, ?_⟩
  intro w
  apply boolOutputAcceptorDescription_haltsOnInput_iff_pointwise hsource b w
  intro T hhalt hmem
  classical
  have hsourceOutput :=
    MachineDescription.haltsWithOutput_of_haltsWithTape hhalt
  have houtput :=
    StoppedMachineDescriptionDecidesLanguage.output_eq_of_haltsWithOutput
      hD hsourceOutput
  cases b
  · by_cases hinput : w ∈ L
    · have hout := houtput.left hinput
      rw [hout] at hmem
      have hfalseTrue : false = true := List.mem_singleton.mp hmem
      cases hfalseTrue
    · exact houtput.right hinput
  · by_cases hinput : w ∈ L
    · exact houtput.left hinput
    · have hout := houtput.right hinput
      rw [hout] at hmem
      have htrueFalse : true = false := List.mem_singleton.mp hmem
      cases htrueFalse

end BoolOutputAcceptor

end Computability
end FoC
