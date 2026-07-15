import FoC.Computability.Compiler.Core.StructuredConstructionTargets.FuelSimulatorCore.Runs.Emission

namespace FoC
namespace Computability

open Languages
open MachineDescription

namespace StructuredConstructionTargets
namespace FuelSimulatorCore
namespace RawLayoutEmission

open EncRewriters.CanonicalLayouts.DovetailStagePrefix
open DovetailInitialLayoutInitializer.StageInputMarkedScanner
open CommonGround.FiniteTransducers
open CommonGround.FiniteTransducers.Structured
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering
open CommonGround.FiniteTransducers.Structured.MultiTapeLowering.ThreeTape

/-- Reverse-order bit stream accumulated by the existing delayed emitter for
an arbitrary nonempty raw Boolean input and a unary fuel value. -/
def rawOutputEmission (attempt : MachineDescription) (fuel : Nat)
    (head : Bool) (tail : Word Bool) : Word Bool :=
  List.append (cellBits false).reverse
    (List.append (cellsBits tail).reverse
      (List.append (stageNatBits tail.length).reverse
        (List.append (cellBits head).reverse
          (List.append (stageNatBits 0).reverse
            (List.append (stageNatBits attempt.start).reverse
              (List.append (stageNatBits fuel).reverse
                (List.append (cellsBits (head :: tail)).reverse
                  (List.append (stageNatBits (head :: tail).length).reverse
                    [false, false, false, false]))))))))

private theorem encodeNatAppend_input
    (n : Nat) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput (encodeNatAppend n suffix) =
      List.append (stageNatBits n) (encodeCodeWordAsInput suffix) := by
  rw [show encodeNatAppend n suffix =
      List.append (encodeNatAppend n []) suffix by
    simpa using encodeNatAppend_append n [] suffix]
  rw [encodeCodeWordAsInput_append]
  simp [encodeNatAppend, stageNatBits]

private theorem encodeCellsAppend_input
    (bits : Word Bool) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput
        (encodeCellsAppend (bits.map some) suffix) =
      List.append (cellsBits bits) (encodeCodeWordAsInput suffix) := by
  rw [show encodeCellsAppend (bits.map some) suffix =
      List.append (encodeCellsAppend (bits.map some) []) suffix by
    simpa using encodeCellsAppend_append (bits.map some) [] suffix]
  rw [encodeCodeWordAsInput_append]
  rfl

private theorem encodeCellAppend_input
    (bit : Bool) (suffix : Word MachineCodeSymbol) :
    encodeCodeWordAsInput (encodeCellAppend (some bit) suffix) =
      List.append (cellBits bit) (encodeCodeWordAsInput suffix) := by
  rw [show encodeCellAppend (some bit) suffix =
      List.append (encodeCellAppend (some bit) []) suffix by
    simpa using encodeCellAppend_append (some bit) [] suffix]
  rw [encodeCodeWordAsInput_append]
  cases bit <;> rfl

theorem rawOutputBits_decomp
    (attempt : MachineDescription) (fuel : Nat)
    (head : Bool) (tail : Word Bool) :
    SimulatorLayout.asBoolInput
        (SimulatorLayout.initial attempt (head :: tail) fuel) =
      List.append [false, false, false, false]
        (List.append (stageNatBits (head :: tail).length)
          (List.append (cellsBits (head :: tail))
            (List.append (stageNatBits fuel)
              (List.append (stageNatBits attempt.start)
                (List.append (stageNatBits 0)
                  (List.append (cellBits head)
                    (List.append (stageNatBits tail.length)
                      (List.append (cellsBits tail)
                        (cellBits false))))))))) := by
  unfold SimulatorLayout.asBoolInput
  rw [simulatorInitial_encode_cons]
  change List.append [false, false, false, false]
    (encodeCodeWordAsInput _) = _
  simp only [encodeCellListAppend, encodeBoolAppend, encodeCellsAppend,
    List.length_map, List.length_cons, List.length_nil,
    encodeNatAppend_input, encodeCellsAppend_input,
    encodeCellAppend_input]
  rfl

theorem rawOutputEmission_reverse
    (attempt : MachineDescription) (fuel : Nat)
    (head : Bool) (tail : Word Bool) :
    (rawOutputEmission attempt fuel head tail).reverse =
      SimulatorLayout.asBoolInput
        (SimulatorLayout.initial attempt (head :: tail) fuel) := by
  rw [rawOutputBits_decomp]
  simp [rawOutputEmission, List.reverse_append, List.append_assoc]

/-- Entry representative expected by the reusable emission suffix.  The
reversed unary fuel lies to the left of a blank separator, followed by the
reversed arbitrary raw input. -/
def rawEmissionEntryScratch (raw : Word Bool) (fuel : Nat) : Tape Bool :=
  tapeAtCells
    (List.append ((stageNatBits fuel).reverse.map some)
      (none :: raw.reverse.map some)) []

/-- Scratch representative left after the generic emission suffix. -/
def rawEmissionFinalScratch (raw : Word Bool) (fuel : Nat) : Tape Bool :=
  tapeAtCells
    (List.append (raw.reverse.map some) [none])
    (none :: List.append ((stageNatBits fuel).map some) [none])

/-- Exact right-shifted serialized initial layout emitted on logical tape 2. -/
def rawEmissionOutputTape (attempt : MachineDescription)
    (raw : Word Bool) (fuel : Nat) : Tape Bool :=
  Tape.move Direction.right
    (SimulatorLayout.tape (SimulatorLayout.initial attempt raw fuel))

/-- The same finite row table, retargeted to enter directly at the generic
emission suffix. -/
def rawEmissionTable (start : Nat) : TypedStateTable State :=
  TypedStateTable.ofList (states start) (.outFalse0 none) .halt (next start)
    (mem_states_emission (h := none) (by simp [emissionBlock]))
    (by simp [states, fixedStates])
    (by intros; rfl)
    (next_target_mem start)

def rawEmissionD (start : Nat) : Description :=
  (rawEmissionTable start).description

theorem rawEmissionTable_config_eq_coreCfg
    (start : Nat) (s : State) (T0 T1 T2 : Tape Bool) :
    (rawEmissionTable start).config s T0 T1 T2 =
      coreCfg start s T0 T1 T2 := by
  rfl

theorem rawEmissionD_stepConfig_eq_coreD
    (start : Nat)
    (c : CommonGround.FiniteTransducers.Structured.Configuration) :
    (rawEmissionD start).stepConfig c =
      (coreD start).stepConfig c := by
  rfl

theorem rawEmissionD_runConfig_eq_coreD
    (start steps : Nat)
    (c : CommonGround.FiniteTransducers.Structured.Configuration) :
    (rawEmissionD start).runConfig steps c =
      (coreD start).runConfig steps c := by
  induction steps generalizing c with
  | zero => rfl
  | succ steps ih =>
      simp only [Description.runConfig]
      rw [rawEmissionD_stepConfig_eq_coreD]
      cases hstep : (coreD start).stepConfig c with
      | none => rfl
      | some next => exact ih next

/-- The emission half of `FuelSimulatorCore` is independent of the original
stage-input parser.  Starting at `outFalse0`, it serializes the exact initial
simulator layout for any nonempty raw Boolean input. -/
theorem leads_halt_from_raw (attempt : MachineDescription)
    (T0 : Tape Bool) (head : Bool) (tail : Word Bool) (fuel : Nat) :
    Leads attempt.start
      (coreCfg attempt.start (.outFalse0 none) T0
        (rawEmissionEntryScratch (head :: tail) fuel) Tape.blank)
      (coreCfg attempt.start .halt T0
        (rawEmissionFinalScratch (head :: tail) fuel)
        (rawEmissionOutputTape attempt (head :: tail) fuel)) := by
  cases hrawRev : (head :: tail).reverse with
  | nil =>
      have : head :: tail = [] := by
        rw [← List.reverse_reverse (head :: tail), hrawRev]
        rfl
      simp at this
  | cons rawLast rawRest =>
      have hreverse : (rawLast :: rawRest).reverse = head :: tail := by
        rw [← hrawRev, List.reverse_reverse]
      have hscan : (head :: tail).reverse = rawLast :: rawRest := by
        rw [← hreverse, List.reverse_reverse]
      have hhead := tailHead_eq_of_reverse_eq hreverse
      have htail := tailStream_eq_of_reverse_eq hreverse
      refine Leads.trans
        (leads_outFalse attempt.start T0
          (rawEmissionEntryScratch (head :: tail) fuel)) ?_
      have hseek :=
        leads_seekFuel attempt.start (some false)
          (stageNatBits fuel).reverse rawLast rawRest T0
          (delayedLeftEmissionTape [true, false, true, false])
      refine Leads.trans (by
        simpa [rawEmissionEntryScratch, hrawRev,
          List.append_assoc] using hseek) ?_
      have htailRun :=
        leads_tailTakeRun attempt.start rawLast rawRest (some false)
          (none :: List.append ((stageNatBits fuel).map some) [none])
          T0 [true, false, true, false] rfl
      refine Leads.trans (by
        simpa [hreverse, hhead, htail,
          List.append_assoc] using htailRun) ?_
      let eTail : Word Bool :=
        List.append [true, false, true, false] (cellsBits tail).reverse
      have htailDone :=
        leads_tailDone attempt.start head eTail.getLast? T0
          (tapeAtCells []
            (none :: some head ::
              List.append (tail.map some)
                (none :: List.append ((stageNatBits fuel).map some) [none])))
          eTail rfl
      refine Leads.trans htailDone ?_
      have htailCount :=
        leads_tailCount attempt.start head tail (some false)
          (List.append ((stageNatBits fuel).map some) [none])
          T0 (List.append eTail [true, true, false, false]) (by simp)
      refine Leads.trans htailCount ?_
      let middleScratch : Tape Bool :=
        tapeAtCells
          (List.append ((head :: tail).reverse.map some) [none])
          (none :: List.append ((stageNatBits fuel).map some) [none])
      let eTailLen : Word Bool :=
        List.append (List.append eTail [true, true, false, false])
          (tickStream tail.length)
      have hheadCell :=
        leads_headCell attempt.start head eTailLen.getLast?
          T0 middleScratch eTailLen rfl
      refine Leads.trans hheadCell ?_
      let eHead : Word Bool :=
        List.append eTailLen [!head, head, true, false]
      have hemptyDone :=
        leads_emptyDone attempt.start (some false)
          T0 middleScratch eHead (by simp [eHead])
      refine Leads.trans hemptyDone ?_
      let eEmpty : Word Bool :=
        List.append eHead [true, true, false, false]
      have hstartDone :=
        leads_startDone attempt.start (some false)
          T0 middleScratch eEmpty (by simp [eEmpty])
      refine Leads.trans hstartDone ?_
      let eStartDone : Word Bool :=
        List.append eEmpty [true, true, false, false]
      have hstartLoop :=
        leads_startLoop attempt.start attempt.start (Nat.le_refl _)
          (some false) T0 middleScratch eStartDone
          (by simp [eStartDone])
      refine Leads.trans hstartLoop ?_
      let eStart : Word Bool :=
        List.append eStartDone (tickStream attempt.start)
      have htoFuelEnd :=
        leads_scratchR
          (start := attempt.start)
          (s := State.fuelSeekStart eStart.getLast?)
          (target := State.fuelSeekEnd eStart.getLast?) (current := none)
          (mem_states_emission (h := eStart.getLast?)
            (by simp [emissionBlock]))
          (by intros; rfl) T0
          (List.append ((head :: tail).reverse.map some) [none])
          (List.append ((stageNatBits fuel).map some) [none])
          (delayedLeftEmissionTape eStart)
      refine Leads.trans htoFuelEnd ?_
      have hfuelScan :=
        leads_fuelSeekEndScan attempt.start eStart.getLast?
          (stageNatBits fuel)
          (none :: List.append ((head :: tail).reverse.map some) [none])
          T0 (delayedLeftEmissionTape eStart)
      refine Leads.trans hfuelScan ?_
      have hfuelNe : stageNatBits fuel ≠ [] := by
        obtain ⟨rest, hrest⟩ := stageNatBits_false_false_tail fuel
        rw [hrest]
        simp
      cases hfuelRev : (stageNatBits fuel).reverse with
      | nil =>
          exfalso
          apply hfuelNe
          rw [← List.reverse_reverse (stageNatBits fuel), hfuelRev]
          rfl
      | cons fuelLast fuelRest =>
          have htoFuelEmit :=
            leads_scratchL
              (start := attempt.start)
              (s := State.fuelSeekEnd eStart.getLast?)
              (target := State.fuelEmit eStart.getLast?) (current := none)
              (mem_states_emission (h := eStart.getLast?)
                (by simp [emissionBlock]))
              (by intros; rfl) T0
              (List.append (fuelRest.map some)
                (none ::
                  List.append ((rawLast :: rawRest).map some) [none]))
              (some fuelLast) [] (delayedLeftEmissionTape eStart)
          refine Leads.trans (by
            simpa [hfuelRev, hscan, List.append_assoc] using htoFuelEmit) ?_
          have hfuelEmit :=
            leads_fuelEmitRev attempt.start eStart.getLast?
              (fuelLast :: fuelRest) rawLast rawRest [none] [none]
              T0 eStart rfl
          refine Leads.trans (by
            simpa [fuelReplayTape, hscan, hfuelRev,
              List.append_assoc] using hfuelEmit) ?_
          have hfuel :
              stageNatBits fuel = (fuelLast :: fuelRest).reverse := by
            rw [← hfuelRev, List.reverse_reverse]
          let eFuel : Word Bool :=
            List.append eStart (fuelLast :: fuelRest)
          have hxCells :=
            leads_xCells attempt.start (rawLast :: rawRest)
              eFuel.getLast?
              (none :: List.append ((stageNatBits fuel).map some) [none])
              T0 eFuel rfl
          have hcell :=
            cellStream_eq_cellsBits_reverse (rawLast :: rawRest)
          let eCells : Word Bool :=
            List.append eFuel (cellStream (rawLast :: rawRest))
          let afterCellsScratch : Tape Bool :=
            tapeAtCells []
              (none ::
                List.append ((rawLast :: rawRest).reverse.map some)
                  (none :: List.append ((stageNatBits fuel).map some) [none]))
          refine Leads.trans
            (d := coreCfg attempt.start (.xDone0 eCells.getLast?)
              T0 afterCellsScratch (delayedLeftEmissionTape eCells))
            (by
              simpa [xCellTape, eFuel, eCells, afterCellsScratch, hfuel,
                List.append_assoc] using hxCells) ?_
          have hxDone :=
            leads_xDone attempt.start eCells.getLast?
              T0 afterCellsScratch eCells rfl
          refine Leads.trans hxDone ?_
          let eXDone : Word Bool :=
            List.append eCells [true, true, false, false]
          have hxCount :=
            leads_xCount attempt.start (rawLast :: rawRest).reverse
              (some false)
              (List.append ((stageNatBits fuel).map some) [none])
              T0 eXDone (by simp [eXDone])
          let eLength : Word Bool :=
            List.append eXDone
              (tickStream (rawLast :: rawRest).reverse.length)
          let afterCountScratch : Tape Bool :=
            tapeAtCells
              (List.append ((rawLast :: rawRest).map some) [none])
              (none :: List.append ((stageNatBits fuel).map some) [none])
          refine Leads.trans
            (d := coreCfg attempt.start (.header0 eLength.getLast?)
              T0 afterCountScratch (delayedLeftEmissionTape eLength))
            (by
              simpa [afterCellsScratch, eXDone, eLength,
                afterCountScratch, List.append_assoc] using hxCount) ?_
          have hheader :=
            leads_header attempt.start eLength.getLast?
              T0 afterCountScratch eLength rfl
          refine Leads.trans hheader ?_
          let eAll : Word Bool :=
            List.append eLength [false, false, false, false]
          have heTail : eTail =
              List.append (cellBits false).reverse
                (cellsBits tail).reverse := by
            rfl
          have heTailLen : eTailLen =
              List.append eTail (stageNatBits tail.length).reverse := by
            rw [stageNatBits_reverse]
            simp [eTailLen, List.append_assoc]
          have heHead : eHead =
              List.append eTailLen (cellBits head).reverse := by
            cases head <;> rfl
          have heEmpty : eEmpty =
              List.append eHead (stageNatBits 0).reverse := by
            rfl
          have heStart : eStart =
              List.append eEmpty (stageNatBits attempt.start).reverse := by
            rw [stageNatBits_reverse]
            simp [eStart, eStartDone, List.append_assoc]
          have hfuelStream : fuelLast :: fuelRest =
              (stageNatBits fuel).reverse := by
            rw [← hfuelRev]
          have heFuel : eFuel =
              List.append eStart (stageNatBits fuel).reverse := by
            simp [eFuel, hfuelStream]
          have heCells : eCells =
              List.append eFuel (cellsBits (head :: tail)).reverse := by
            simp [eCells, hcell, hreverse]
          have heLength : eLength =
              List.append eCells
                (stageNatBits (head :: tail).length).reverse := by
            rw [stageNatBits_reverse]
            simp [eLength, eXDone, hreverse, List.append_assoc]
          have hemission :
              eAll = rawOutputEmission attempt fuel head tail := by
            rw [show eAll =
                List.append eLength [false, false, false, false] from rfl,
              heLength, heCells, heFuel, heStart, heEmpty, heHead,
              heTailLen, heTail]
            simp [rawOutputEmission, List.append_assoc]
          have hfinish :=
            leads_finish attempt.start (some false)
              T0 afterCountScratch eAll (by simp [eAll])
          have hscratch :
              afterCountScratch =
                rawEmissionFinalScratch (head :: tail) fuel := by
            simp [afterCountScratch, rawEmissionFinalScratch, hrawRev]
          have hout :
              Tape.move Direction.right (Tape.input eAll.reverse) =
                rawEmissionOutputTape attempt (head :: tail) fuel := by
            rw [hemission, rawOutputEmission_reverse]
            rfl
          simpa only [hscratch, hout] using hfinish

end RawLayoutEmission
end FuelSimulatorCore
end StructuredConstructionTargets

end Computability
end FoC
