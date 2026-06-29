import FoC.Computability.Compiler.UniversalAndRanges.FiniteSource.Normalizer.Soundness.TransitionBlock.Steps

set_option doc.verso true

namespace FoC
namespace Computability

open Languages

def codePrefixParserNormalizerMarkedContextLeft
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks count : Nat)
    (pre : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  List.append
    ((List.append
      (List.append
        (List.replicate blanks MachineCodeSymbol.blank)
        (MachineDescription.encodeNat count))
      pre).reverse.map some)
    (none :: prefixLeft)

def codePrefixParserNormalizerRestoredTail
    (pre input : Word MachineCodeSymbol) :
    List (Option MachineCodeSymbol) :=
  List.append (pre.map some)
    (match input with
    | [] => [none]
    | symbol :: suffix => some symbol :: suffix.map some)

theorem codePrefixParserNormalizerRestoredTail_normalized
    (pre input : Word MachineCodeSymbol) :
    (codePrefixParserNormalizerRestoredTail pre input).filterMap
        (fun cell => cell) =
      List.append pre input := by
  cases input <;>
    simp [codePrefixParserNormalizerRestoredTail,
      codePrefixParserNormalizer_filterMap_comp_some,
      List.filterMap_append]

theorem codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition_saved
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks count : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (saved : Option MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks (count + 1) pre)
            (saved :: suffix.map some) }
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft (blanks + 1) count pre)
            (saved :: suffix.map some) } := by
  let leftNormal : Word MachineCodeSymbol :=
    List.append
      (List.append
        (List.replicate blanks MachineCodeSymbol.blank)
        (MachineDescription.encodeNat (count + 1)))
      pre
  let countTail : Word MachineCodeSymbol :=
    List.append pre (MachineCodeSymbol.header :: suffix)
  let countLeft : List (Option MachineCodeSymbol) :=
    List.append
      ((MachineDescription.encodeNat count).reverse.map some)
      (some MachineCodeSymbol.blank ::
        List.append
          (List.replicate blanks (some MachineCodeSymbol.blank))
          (none :: prefixLeft))
  let targetLeft : List (Option MachineCodeSymbol) :=
    codePrefixParserNormalizerMarkedContextLeft
      prefixLeft (blanks + 1) count pre
  have hrevNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal, MachineDescription.encodeNat]
  cases hrev : leftNormal.reverse with
  | nil =>
      exact False.elim (hrevNonempty hrev)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa using h
      have hprefix :
          List.append (leftSymbols.reverse.map some) [some current] =
            leftNormal.map some := by
        have hmap :=
          congrArg (fun xs : List MachineCodeSymbol => xs.map some)
            hleft
        simpa [List.map_append, List.map_reverse,
          List.append_assoc] using hmap.symm
      have hleftStart :
          codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks (count + 1) pre =
            some current ::
              List.append (leftSymbols.map some) (none :: prefixLeft) := by
        have hmapRev :
            List.append (leftNormal.reverse.map some)
                (none :: prefixLeft) =
              some current ::
                List.append (leftSymbols.map some)
                  (none :: prefixLeft) := by
          simp [hrev]
        simpa [codePrefixParserNormalizerMarkedContextLeft,
          leftNormal, List.append_assoc] using hmapRev
      have hreturn :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.markPosition
              tape :=
                transitionListParserOptionTape
                  (codePrefixParserNormalizerMarkedContextLeft
                    prefixLeft blanks (count + 1) pre)
                  (saved :: suffix.map some) }
            { state :=
                CodePrefixParserNormalizerState.findCount
                  (TransitionListParserMarker.saved saved)
              tape :=
                transitionListParserOptionTape (none :: prefixLeft)
                  (List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header ::
                      suffix.map some)) } := by
        have hrun :=
          codePrefixParserNormalizerMachine_markPosition_returnLeft_toBoundary
            saved leftSymbols prefixLeft current
            (suffix.map some)
        have htargetRest :
            List.append (List.map some leftSymbols).reverse
                (some current ::
                  some MachineCodeSymbol.header ::
                    suffix.map some) =
              List.append (leftNormal.map some)
                (some MachineCodeSymbol.header ::
                  suffix.map some) := by
          calc
            List.append (List.map some leftSymbols).reverse
                (some current ::
                  some MachineCodeSymbol.header ::
                    suffix.map some)
                =
              List.append
                (List.append (List.map some leftSymbols).reverse
                  [some current])
                (some MachineCodeSymbol.header ::
                  suffix.map some) := by
                  simp [List.append_assoc]
            _ =
              List.append (leftNormal.map some)
                (some MachineCodeSymbol.header ::
                  suffix.map some) := by
                  simpa [List.map_reverse] using
                    congrArg
                      (fun xs => List.append xs
                        (some MachineCodeSymbol.header ::
                          suffix.map some))
                      hprefix
        rw [hleftStart]
        rw [← htargetRest]
        simpa [List.map_reverse] using hrun
      have hfind :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state :=
                CodePrefixParserNormalizerState.findCount
                  (TransitionListParserMarker.saved saved)
              tape :=
                transitionListParserOptionTape (none :: prefixLeft)
                  (List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header ::
                      suffix.map some)) }
            { state :=
                CodePrefixParserNormalizerState.seekCountDone
                  (TransitionListParserMarker.saved saved)
              tape :=
                transitionListParserOptionTape
                  (some MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (none :: prefixLeft))
                  ((MachineDescription.encodeNatAppend count
                    countTail).map some) } := by
        have hrun :=
          codePrefixParserNormalizerMachine_computes_findCount_blanks_tick
            (TransitionListParserMarker.saved saved)
            blanks (none :: prefixLeft)
            ((MachineDescription.encodeNatAppend count countTail).map some)
        simpa [leftNormal, countTail, MachineDescription.encodeNat,
          MachineDescription.encodeNatAppend, List.map_append,
          List.map_replicate, List.append_assoc] using hrun
      have hseek :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state :=
                CodePrefixParserNormalizerState.seekCountDone
                  (TransitionListParserMarker.saved saved)
              tape :=
                transitionListParserOptionTape
                  (some MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (none :: prefixLeft))
                  ((MachineDescription.encodeNatAppend count
                    countTail).map some) }
            { state :=
                CodePrefixParserNormalizerState.seekMarker saved
              tape :=
                transitionListParserOptionTape countLeft
                  (countTail.map some) } := by
        simpa [countLeft] using
          codePrefixParserNormalizerMachine_computes_seekCountDone_saved
            saved
            (some MachineCodeSymbol.blank ::
              List.append
                (List.replicate blanks (some MachineCodeSymbol.blank))
                (none :: prefixLeft))
            count countTail
      have hscan :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state :=
                CodePrefixParserNormalizerState.seekMarker saved
              tape :=
                transitionListParserOptionTape countLeft
                  (countTail.map some) }
            { state :=
                CodePrefixParserNormalizerState.seekMarker saved
              tape :=
                transitionListParserOptionTape targetLeft
                  (some MachineCodeSymbol.header ::
                    suffix.map some) } := by
        have hrun :=
          codePrefixParserNormalizerMachine_seekMarker_scan_noHeader
            saved pre hpre countLeft
            (suffix.map some)
        have hblank :
            some MachineCodeSymbol.blank ::
                List.append
                  (List.replicate blanks
                    (some MachineCodeSymbol.blank))
                  (none :: prefixLeft) =
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                  (some MachineCodeSymbol.blank ::
                  none :: prefixLeft) := by
          calc
            some MachineCodeSymbol.blank ::
                List.append
                  (List.replicate blanks
                    (some MachineCodeSymbol.blank))
                  (none :: prefixLeft)
                =
              List.append
                (List.replicate (blanks + 1)
                  (some MachineCodeSymbol.blank))
                (none :: prefixLeft) := by
                simp [List.replicate_succ]
            _ =
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                (some MachineCodeSymbol.blank ::
                  none :: prefixLeft) := by
                exact
                  (codePrefixParserNormalizer_replicate_append_self
                    (some MachineCodeSymbol.blank) blanks
                    (none :: prefixLeft)).symm
        have htargetLeft :
            targetLeft =
              List.append (pre.reverse.map some)
                (List.append
                  ((MachineDescription.encodeNat count).reverse.map some)
                  (some MachineCodeSymbol.blank ::
                    List.append
                      (List.replicate blanks
                        (some MachineCodeSymbol.blank))
                      (none :: prefixLeft))) := by
          simpa [targetLeft, codePrefixParserNormalizerMarkedContextLeft,
            List.reverse_append, List.map_append, List.map_reverse,
            List.map_replicate, List.replicate_succ,
            List.append_assoc] using hblank.symm
        rw [htargetLeft]
        simpa [countTail, countLeft, List.map_append,
          List.append_assoc] using hrun
      have htargetNonempty : targetLeft ≠ [] := by
        simp [targetLeft, codePrefixParserNormalizerMarkedContextLeft]
      cases htarget : targetLeft with
      | nil =>
          exact False.elim (htargetNonempty htarget)
      | cons leftHead leftTail =>
          have hheader :
              TuringMachine.Step codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.seekMarker saved
                  tape :=
                    transitionListParserOptionTape targetLeft
                      (some MachineCodeSymbol.header ::
                        suffix.map some) }
                { state :=
                    CodePrefixParserNormalizerState.enterMarkedPosition
                  tape :=
                    transitionListParserOptionTape leftTail
                      (leftHead :: saved :: suffix.map some) } := by
            rw [htarget]
            exact
              codePrefixParserNormalizerMachine_step_seekMarker_header
                saved leftTail (suffix.map some) leftHead
          have henter :
              TuringMachine.Step codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.enterMarkedPosition
                  tape :=
                    transitionListParserOptionTape leftTail
                      (leftHead :: saved :: suffix.map some) }
                { state := CodePrefixParserNormalizerState.needTransition
                  tape :=
                    transitionListParserOptionTape targetLeft
                      (saved :: suffix.map some) } := by
            rw [htarget]
            exact
              codePrefixParserNormalizerMachine_step_enterMarkedPosition
                leftTail (saved :: suffix.map some) leftHead
          exact
            TuringMachine.computes_trans hreturn
              (TuringMachine.computes_trans hfind
                (TuringMachine.computes_trans hseek
                  (TuringMachine.computes_trans hscan
                      (TuringMachine.Computes.step hheader
                        (TuringMachine.Computes.step henter
                          (TuringMachine.Computes.refl _))))))

theorem codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks count : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre)
    (symbol : MachineCodeSymbol) (suffix : Word MachineCodeSymbol) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks (count + 1) pre)
            ((symbol :: suffix).map some) }
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft (blanks + 1) count pre)
            ((symbol :: suffix).map some) } := by
  simpa using
    codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition_saved
      prefixLeft blanks count pre hpre (some symbol) suffix

theorem codePrefixParserNormalizerMachine_computes_markPosition_context_empty_to_needTransition
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks count : Nat)
    (pre : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks (count + 1) pre)
            [] }
      { state := CodePrefixParserNormalizerState.needTransition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft (blanks + 1) count pre)
            [none] } := by
  simpa using
    codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition_saved
      prefixLeft blanks count pre hpre none []

theorem codePrefixParserNormalizerMachine_computes_markPosition_context_zero_halt
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks : Nat)
    (pre input : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks 0 pre)
            (input.map some) }
      { state := CodePrefixParserNormalizerState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              codePrefixParserNormalizerRestoredTicksLeft blanks
                (some MachineCodeSymbol.done :: prefixLeft))
            (codePrefixParserNormalizerRestoredTail pre input) } := by
  let leftNormal : Word MachineCodeSymbol :=
    List.append
      (List.append
        (List.replicate blanks MachineCodeSymbol.blank)
        (MachineDescription.encodeNat 0))
      pre
  have hrevNonempty : leftNormal.reverse ≠ [] := by
    simp [leftNormal, MachineDescription.encodeNat]
  cases hrev : leftNormal.reverse with
  | nil =>
      exact False.elim (hrevNonempty hrev)
  | cons current leftSymbols =>
      have hleft :
          leftNormal = List.append leftSymbols.reverse [current] := by
        have h := congrArg List.reverse hrev
        simpa using h
      have hprefix :
          List.append (List.map some leftSymbols).reverse [some current] =
            leftNormal.map some := by
        have hmap :=
          congrArg (fun xs : List MachineCodeSymbol => xs.map some)
            hleft
        simpa [List.map_append, List.map_reverse,
          List.append_assoc] using hmap.symm
      have hleftStart :
          codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks 0 pre =
            some current ::
              List.append (leftSymbols.map some) (none :: prefixLeft) := by
        have hmapRev :
            List.append (leftNormal.reverse.map some)
                (none :: prefixLeft) =
              some current ::
                List.append (leftSymbols.map some)
                  (none :: prefixLeft) := by
          simp [hrev]
        simpa [codePrefixParserNormalizerMarkedContextLeft,
          leftNormal, List.append_assoc] using hmapRev
      cases input with
      | nil =>
          have hreturn :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      [] }
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      (TransitionListParserMarker.saved none)
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        [some MachineCodeSymbol.header]) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_markPosition_empty_returnLeft_toBoundary
                leftSymbols prefixLeft current
            have htargetRest :
                List.append (List.map some leftSymbols).reverse
                    [some current, some MachineCodeSymbol.header] =
                  List.append (leftNormal.map some)
                    [some MachineCodeSymbol.header] := by
              calc
                List.append (List.map some leftSymbols).reverse
                    [some current, some MachineCodeSymbol.header]
                    =
                  List.append
                    (List.append (List.map some leftSymbols).reverse
                      [some current])
                    [some MachineCodeSymbol.header] := by
                    simp [List.append_assoc]
                _ =
                  List.append (leftNormal.map some)
                    [some MachineCodeSymbol.header] := by
                    simpa using
                      congrArg
                        (fun xs => List.append xs
                          [some MachineCodeSymbol.header])
                        hprefix
            rw [hleftStart]
            rw [← htargetRest]
            simpa [List.map_reverse] using hrun
          have hfind :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      (TransitionListParserMarker.saved none)
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        [some MachineCodeSymbol.header]) }
                { state := CodePrefixParserNormalizerState.restoreSeekMarker none
                  tape :=
                    transitionListParserOptionTape
                      (some MachineCodeSymbol.done ::
                        List.append
                          (List.replicate blanks
                            (some MachineCodeSymbol.blank))
                          (none :: prefixLeft))
                      (List.append (pre.map some)
                        [some MachineCodeSymbol.header]) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_computes_findCount_saved_blanks_done
                none blanks (none :: prefixLeft)
                (List.append (pre.map some)
                  [some MachineCodeSymbol.header])
            simpa [leftNormal, MachineDescription.encodeNat,
              List.map_append, List.map_replicate,
              List.append_assoc] using hrun
          let scanLeft : List (Option MachineCodeSymbol) :=
            some MachineCodeSymbol.done ::
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                (none :: prefixLeft)
          have hscan :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.restoreSeekMarker none
                  tape :=
                    transitionListParserOptionTape scanLeft
                      (List.append (pre.map some)
                        [some MachineCodeSymbol.header]) }
                { state := CodePrefixParserNormalizerState.restoreSeekMarker none
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      [some MachineCodeSymbol.header] } := by
            have hrun :=
              codePrefixParserNormalizerMachine_restoreSeekMarker_scan_noHeader
                none pre hpre scanLeft []
            have htargetLeft :
                codePrefixParserNormalizerMarkedContextLeft
                    prefixLeft blanks 0 pre =
                  List.append (pre.reverse.map some) scanLeft := by
              simp [scanLeft, codePrefixParserNormalizerMarkedContextLeft,
                MachineDescription.encodeNat, List.reverse_append,
                List.map_append, List.map_reverse, List.map_replicate,
                List.append_assoc]
            rw [htargetLeft]
            simpa [scanLeft, List.map_append, List.append_assoc] using hrun
          have hrestore :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.restoreSeekMarker none
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      [some MachineCodeSymbol.header] }
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      TransitionListParserMarker.initial
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some) [none]) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_restoreSeekMarker_toBoundary
                none leftSymbols prefixLeft current []
            have htargetRest :
                List.append (List.map some leftSymbols).reverse
                    [some current, none] =
                  List.append (leftNormal.map some) [none] := by
              calc
                List.append (List.map some leftSymbols).reverse
                    [some current, none]
                    =
                  List.append
                    (List.append (List.map some leftSymbols).reverse
                      [some current])
                    [none] := by
                    simp [List.append_assoc]
                _ =
                  List.append (leftNormal.map some) [none] := by
                    simpa using
                      congrArg
                        (fun xs => List.append xs [none])
                        hprefix
            rw [hleftStart]
            rw [← htargetRest]
            simpa [List.map_reverse] using hrun
          have hfinish :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      TransitionListParserMarker.initial
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some) [none]) }
                { state := CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      (some MachineCodeSymbol.done ::
                        codePrefixParserNormalizerRestoredTicksLeft blanks
                          (some MachineCodeSymbol.done :: prefixLeft))
                      (codePrefixParserNormalizerRestoredTail pre []) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_computes_findCount_initial_blanks_done_halt
                blanks prefixLeft
                (codePrefixParserNormalizerRestoredTail pre [])
            simpa [leftNormal, MachineDescription.encodeNat,
              codePrefixParserNormalizerRestoredTail, List.map_append,
              List.map_replicate, List.append_assoc] using hrun
          exact
            TuringMachine.computes_trans hreturn
              (TuringMachine.computes_trans hfind
                (TuringMachine.computes_trans
                  (by simpa [scanLeft] using hscan)
                  (TuringMachine.computes_trans hrestore hfinish)))
      | cons symbol suffix =>
          have hreturn :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      (some symbol :: suffix.map some) }
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      (TransitionListParserMarker.saved
                        (some symbol))
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        (some MachineCodeSymbol.header ::
                          suffix.map some)) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_markPosition_returnLeft_toBoundary
                (some symbol) leftSymbols prefixLeft current
                (suffix.map some)
            have htargetRest :
                List.append (List.map some leftSymbols).reverse
                    (some current ::
                      some MachineCodeSymbol.header ::
                        suffix.map some) =
                  List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header ::
                      suffix.map some) := by
              calc
                List.append (List.map some leftSymbols).reverse
                    (some current ::
                      some MachineCodeSymbol.header ::
                        suffix.map some)
                    =
                  List.append
                    (List.append (List.map some leftSymbols).reverse
                      [some current])
                    (some MachineCodeSymbol.header ::
                      suffix.map some) := by
                    simp [List.append_assoc]
                _ =
                  List.append (leftNormal.map some)
                    (some MachineCodeSymbol.header ::
                      suffix.map some) := by
                    simpa using
                      congrArg
                        (fun xs => List.append xs
                          (some MachineCodeSymbol.header ::
                            suffix.map some))
                        hprefix
            rw [hleftStart]
            rw [← htargetRest]
            simpa [List.map_reverse] using hrun
          have hfind :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      (TransitionListParserMarker.saved
                        (some symbol))
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        (some MachineCodeSymbol.header ::
                          suffix.map some)) }
                { state :=
                    CodePrefixParserNormalizerState.restoreSeekMarker
                      (some symbol)
                  tape :=
                    transitionListParserOptionTape
                      (some MachineCodeSymbol.done ::
                        List.append
                          (List.replicate blanks
                            (some MachineCodeSymbol.blank))
                          (none :: prefixLeft))
                      (List.append (pre.map some)
                        (some MachineCodeSymbol.header ::
                          suffix.map some)) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_computes_findCount_saved_blanks_done
                (some symbol) blanks (none :: prefixLeft)
                (List.append (pre.map some)
                  (some MachineCodeSymbol.header :: suffix.map some))
            simpa [leftNormal, MachineDescription.encodeNat,
              List.map_append, List.map_replicate,
              List.append_assoc] using hrun
          let scanLeft : List (Option MachineCodeSymbol) :=
            some MachineCodeSymbol.done ::
              List.append
                (List.replicate blanks
                  (some MachineCodeSymbol.blank))
                (none :: prefixLeft)
          have hscan :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.restoreSeekMarker
                      (some symbol)
                  tape :=
                    transitionListParserOptionTape scanLeft
                      (List.append (pre.map some)
                        (some MachineCodeSymbol.header ::
                          suffix.map some)) }
                { state :=
                    CodePrefixParserNormalizerState.restoreSeekMarker
                      (some symbol)
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      (some MachineCodeSymbol.header ::
                        suffix.map some) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_restoreSeekMarker_scan_noHeader
                (some symbol) pre hpre scanLeft suffix
            have htargetLeft :
                codePrefixParserNormalizerMarkedContextLeft
                    prefixLeft blanks 0 pre =
                  List.append (pre.reverse.map some) scanLeft := by
              simp [scanLeft, codePrefixParserNormalizerMarkedContextLeft,
                MachineDescription.encodeNat, List.reverse_append,
                List.map_append, List.map_reverse, List.map_replicate,
                List.append_assoc]
            rw [htargetLeft]
            simpa [scanLeft, List.map_append, List.append_assoc] using hrun
          have hrestore :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.restoreSeekMarker
                      (some symbol)
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft blanks 0 pre)
                      (some MachineCodeSymbol.header ::
                        suffix.map some) }
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      TransitionListParserMarker.initial
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        (some symbol :: suffix.map some)) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_restoreSeekMarker_toBoundary
                (some symbol) leftSymbols prefixLeft current
                (suffix.map some)
            have htargetRest :
                List.append (List.map some leftSymbols).reverse
                    (some current ::
                      some symbol :: suffix.map some) =
                  List.append (leftNormal.map some)
                    (some symbol :: suffix.map some) := by
              calc
                List.append (List.map some leftSymbols).reverse
                    (some current ::
                      some symbol :: suffix.map some)
                    =
                  List.append
                    (List.append (List.map some leftSymbols).reverse
                      [some current])
                    (some symbol :: suffix.map some) := by
                    simp [List.append_assoc]
                _ =
                  List.append (leftNormal.map some)
                    (some symbol :: suffix.map some) := by
                    simpa using
                      congrArg
                        (fun xs => List.append xs
                          (some symbol :: suffix.map some))
                        hprefix
            rw [hleftStart]
            rw [← htargetRest]
            simpa [List.map_reverse] using hrun
          have hfinish :
              TuringMachine.Computes codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.findCount
                      TransitionListParserMarker.initial
                  tape :=
                    transitionListParserOptionTape (none :: prefixLeft)
                      (List.append (leftNormal.map some)
                        (some symbol :: suffix.map some)) }
                { state := CodePrefixParserNormalizerState.halt
                  tape :=
                    transitionListParserOptionTape
                      (some MachineCodeSymbol.done ::
                        codePrefixParserNormalizerRestoredTicksLeft blanks
                          (some MachineCodeSymbol.done :: prefixLeft))
                      (codePrefixParserNormalizerRestoredTail pre
                        (symbol :: suffix)) } := by
            have hrun :=
              codePrefixParserNormalizerMachine_computes_findCount_initial_blanks_done_halt
                blanks prefixLeft
                (codePrefixParserNormalizerRestoredTail pre
                  (symbol :: suffix))
            simpa [leftNormal, MachineDescription.encodeNat,
              codePrefixParserNormalizerRestoredTail, List.map_append,
              List.map_replicate, List.append_assoc] using hrun
          exact
            TuringMachine.computes_trans hreturn
              (TuringMachine.computes_trans hfind
                (TuringMachine.computes_trans
                  (by simpa [scanLeft] using hscan)
                  (TuringMachine.computes_trans hrestore hfinish)))

theorem codePrefixParserNormalizerMachine_computes_markPosition_context_halt
    (prefixLeft : List (Option MachineCodeSymbol))
    (blanks : Nat)
    (pre : Word MachineCodeSymbol)
    (rest : List TransitionDescription)
    (input : Word MachineCodeSymbol)
    (hpre : transitionListParserNoHeader pre) :
    TuringMachine.Computes codePrefixParserNormalizerMachine
      { state := CodePrefixParserNormalizerState.markPosition
        tape :=
          transitionListParserOptionTape
            (codePrefixParserNormalizerMarkedContextLeft
              prefixLeft blanks rest.length pre)
            ((MachineDescription.encodeTransitionsAppend rest input).map
              some) }
      { state := CodePrefixParserNormalizerState.halt
        tape :=
          transitionListParserOptionTape
            (some MachineCodeSymbol.done ::
              codePrefixParserNormalizerRestoredTicksLeft
                (blanks + rest.length)
                (some MachineCodeSymbol.done :: prefixLeft))
            (codePrefixParserNormalizerRestoredTail
              (List.append pre
                (MachineDescription.encodeTransitions rest))
              input) } := by
  induction rest generalizing blanks pre with
  | nil =>
      simpa [MachineDescription.encodeTransitions,
        MachineDescription.encodeTransitionsAppend] using
        codePrefixParserNormalizerMachine_computes_markPosition_context_zero_halt
          prefixLeft blanks pre input hpre
  | cons transition rest ih =>
      let afterTransition : Word MachineCodeSymbol :=
        MachineDescription.encodeNatAppend transition.source
          (MachineDescription.encodeCellAppend transition.read
            (MachineDescription.encodeCellAppend transition.write
              (MachineDescription.encodeDirectionAppend transition.move
                (MachineDescription.encodeNatAppend transition.target
                  (MachineDescription.encodeTransitionsAppend rest input)))))
      have htokens :
          MachineDescription.encodeTransitionsAppend
              (transition :: rest) input =
            MachineCodeSymbol.transition :: afterTransition := by
        simp [afterTransition,
          MachineDescription.encodeTransitionsAppend,
          MachineDescription.encodeTransitionAppend]
      have hstep :=
        codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition
          prefixLeft blanks rest.length pre hpre
          MachineCodeSymbol.transition afterTransition
      have hparse :=
        codePrefixParserNormalizerMachine_computes_transition
          transition
          (codePrefixParserNormalizerMarkedContextLeft
            prefixLeft (blanks + 1) rest.length pre)
          (MachineDescription.encodeTransitionsAppend rest input)
      have hpre' :
          transitionListParserNoHeader
            (List.append pre
              (MachineDescription.encodeTransition transition)) :=
        transitionListParserNoHeader_append hpre
          (transitionListParser_encodeTransition_noHeader transition)
      have htail :=
        ih (blanks + 1)
          (List.append pre
            (MachineDescription.encodeTransition transition))
          hpre'
      have hparse' :
          TuringMachine.Computes codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.needTransition
              tape :=
                transitionListParserOptionTape
                  (codePrefixParserNormalizerMarkedContextLeft
                    prefixLeft (blanks + 1) rest.length pre)
                  ((MachineDescription.encodeTransitionsAppend
                    (transition :: rest) input).map some) }
            { state := CodePrefixParserNormalizerState.markPosition
              tape :=
                transitionListParserOptionTape
                  (codePrefixParserNormalizerMarkedContextLeft
                    prefixLeft (blanks + 1) rest.length
                    (List.append pre
                      (MachineDescription.encodeTransition transition)))
                  ((MachineDescription.encodeTransitionsAppend rest input).map
                    some) } := by
        simpa [codePrefixParserNormalizerMarkedContextLeft,
          MachineDescription.encodeTransitionsAppend,
          MachineDescription.encodeTransition,
          MachineDescription.encodeTransitionAppend,
          MachineDescription.encodeNatAppend,
          MachineDescription.encodeCellAppend,
          MachineDescription.encodeDirectionAppend,
          List.reverse_append, List.map_append, List.map_reverse,
          List.map_replicate, List.append_assoc] using hparse
      exact
        TuringMachine.computes_trans
          (by simpa [htokens] using hstep)
          (TuringMachine.computes_trans hparse'
            (by
              simpa [MachineDescription.encodeTransitions,
                MachineDescription.encodeTransitionsAppend,
                MachineDescription.encodeTransition,
                MachineDescription.encodeTransitionAppend,
                MachineDescription.encodeNatAppend,
                MachineDescription.encodeCellAppend,
                MachineDescription.encodeDirectionAppend,
                  List.append_assoc, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using htail))

theorem codePrefixParserNormalizerMachine_haltsFrom_markPosition_context_inv
    (prefixLeft : List (Option MachineCodeSymbol))
    (count : Nat) :
    forall (blanks : Nat) (pre tokens : Word MachineCodeSymbol),
      transitionListParserNoHeader pre ->
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.markPosition
          tape :=
            transitionListParserOptionTape
              (codePrefixParserNormalizerMarkedContextLeft
                prefixLeft blanks count pre)
              (tokens.map some) } ->
      exists transitions : List TransitionDescription,
      exists suffix : Word MachineCodeSymbol,
        count = transitions.length ∧
          tokens =
            MachineDescription.encodeTransitionsAppend transitions suffix := by
  induction count with
  | zero =>
      intro blanks pre tokens hpre h
      exact ⟨[], tokens, rfl, rfl⟩
  | succ count ih =>
      intro blanks pre tokens hpre h
      cases tokens with
      | nil =>
          have hneed :
              TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft (blanks + 1) count pre)
                      [none] } :=
            codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
              (codePrefixParserNormalizerMachine_computes_markPosition_context_empty_to_needTransition
                prefixLeft blanks count pre hpre)
              h
          exact False.elim
            ((codePrefixParserNormalizerMachine_not_haltsFrom_needTransition_none
                (codePrefixParserNormalizerMarkedContextLeft
                  prefixLeft (blanks + 1) count pre)
                [])
              hneed)
      | cons symbol rest =>
          have hneed :
              TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.needTransition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft (blanks + 1) count pre)
                      ((symbol :: rest).map some) } :=
            codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
              (codePrefixParserNormalizerMachine_computes_markPosition_context_to_needTransition
                prefixLeft blanks count pre hpre symbol rest)
              h
          rcases
              codePrefixParserNormalizerMachine_haltsFrom_needTransition_inv
                hneed with
            ⟨t, restTokens, htokens, hmarkFrom⟩
          have hpre' :
              transitionListParserNoHeader
                (List.append pre
                  (MachineDescription.encodeTransition t)) :=
            transitionListParserNoHeader_append hpre
              (transitionListParser_encodeTransition_noHeader t)
          have hmarkContext :
              TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft (blanks + 1) count
                        (List.append pre
                          (MachineDescription.encodeTransition t)))
                      (restTokens.map some) } := by
            simpa [codePrefixParserNormalizerMarkedContextLeft,
              MachineDescription.encodeTransition,
              MachineDescription.encodeTransitionAppend,
              MachineDescription.encodeNatAppend,
              MachineDescription.encodeCellAppend,
              MachineDescription.encodeDirectionAppend,
              List.reverse_append, List.map_append, List.map_reverse,
              List.map_replicate, List.append_assoc] using hmarkFrom
          rcases
              ih (blanks + 1)
                (List.append pre
                  (MachineDescription.encodeTransition t))
                restTokens hpre' hmarkContext with
            ⟨transitions, suffix, hcount, hrestTokens⟩
          refine ⟨t :: transitions, suffix, ?_, ?_⟩
          · simp [hcount]
          · simp [MachineDescription.encodeTransitionsAppend,
              htokens, hrestTokens]

theorem codePrefixParserNormalizerMachine_haltsFrom_findInitialCount_decodeTransitions
    (prefixLeft : List (Option MachineCodeSymbol))
    {transitionBlock : Word MachineCodeSymbol}
    (h :
      TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
        { state := CodePrefixParserNormalizerState.findInitialCount
          tape :=
            transitionListParserOptionTape (none :: prefixLeft)
              (transitionBlock.map some) }) :
    exists transitionCount : Nat,
    exists rest : Word MachineCodeSymbol,
    exists transitions : List TransitionDescription,
    exists input : Word MachineCodeSymbol,
      transitionBlock =
          MachineDescription.encodeNatAppend transitionCount rest ∧
        MachineDescription.decodeTransitions transitionCount rest =
          some (transitions, input) := by
  cases transitionBlock with
  | nil =>
      exact False.elim
        ((codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck
            (by simp [TuringMachine.Halted,
              codePrefixParserNormalizerMachine])
            (by
              intro d hstep
              cases hstep with
              | mk htransition =>
                  simp [codePrefixParserNormalizerMachine,
                    transitionListParserOptionTape, Tape.read] at htransition))
          h)
  | cons symbol rest =>
      have hstuck
          (hsymbol :
            symbol ≠ MachineCodeSymbol.tick ∧
              symbol ≠ MachineCodeSymbol.done) :
          ¬ TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
            { state := CodePrefixParserNormalizerState.findInitialCount
              tape :=
                transitionListParserOptionTape (none :: prefixLeft)
                  ((symbol :: rest).map some) } := by
        refine codePrefixParserNormalizerMachine_not_haltsFrom_of_stuck ?_ ?_
        · simp [TuringMachine.Halted, codePrefixParserNormalizerMachine]
        · intro d hstep
          cases hstep with
          | mk htransition =>
              cases symbol <;>
                simp [codePrefixParserNormalizerMachine,
                  transitionListParserOptionTape, Tape.read] at hsymbol htransition
      cases symbol with
      | done =>
          exact ⟨0, rest, [], rest, rfl, rfl⟩
      | tick =>
          have hseek :
              TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
                { state :=
                    CodePrefixParserNormalizerState.seekCountDone
                      TransitionListParserMarker.initial
                  tape :=
                    transitionListParserOptionTape
                      (some MachineCodeSymbol.blank :: none :: prefixLeft)
                      (rest.map some) } :=
            codePrefixParserNormalizerMachine_halts_from_of_computes_suffix
              (TuringMachine.computes_of_step
                (codePrefixParserNormalizerMachine_step_findInitialCount_tick
                  (none :: prefixLeft) (rest.map some)))
              h
          rcases
              codePrefixParserNormalizerMachine_haltsFrom_seekCountDone_initial_inv
                hseek with
            ⟨count, suffix, hrest, hneed⟩
          rcases
              codePrefixParserNormalizerMachine_haltsFrom_needTransition_inv
                (by
                  simpa [codePrefixParserNormalizerMarkedContextLeft,
                    MachineDescription.encodeNat, List.append_assoc] using
                    hneed) with
            ⟨t, restTokens, htokens, hmarkFrom⟩
          have hpre :
              transitionListParserNoHeader
                (MachineDescription.encodeTransition t) :=
            transitionListParser_encodeTransition_noHeader t
          have hmarkContext :
              TuringMachine.HaltsFrom codePrefixParserNormalizerMachine
                { state := CodePrefixParserNormalizerState.markPosition
                  tape :=
                    transitionListParserOptionTape
                      (codePrefixParserNormalizerMarkedContextLeft
                        prefixLeft 1 count
                        (MachineDescription.encodeTransition t))
                      (restTokens.map some) } := by
            simpa [codePrefixParserNormalizerMarkedContextLeft,
              MachineDescription.encodeTransition,
              MachineDescription.encodeTransitionAppend,
              MachineDescription.encodeNatAppend,
              MachineDescription.encodeCellAppend,
              MachineDescription.encodeDirectionAppend,
              List.reverse_append, List.map_append, List.map_reverse,
              List.map_replicate, List.append_assoc] using hmarkFrom
          rcases
              codePrefixParserNormalizerMachine_haltsFrom_markPosition_context_inv
                prefixLeft count 1
                (MachineDescription.encodeTransition t)
                restTokens hpre hmarkContext with
            ⟨transitions, input, hcount, hrestTokens⟩
          refine ⟨count + 1, suffix, t :: transitions, input, ?_, ?_⟩
          · simp [MachineDescription.encodeNatAppend,
              MachineDescription.encodeNat, hrest]
          · simpa [hcount, htokens, hrestTokens,
              MachineDescription.encodeTransitionsAppend] using
              MachineDescription.decodeTransitions_encodeTransitions_append
                (t :: transitions) input
      | header =>
          exact False.elim (hstuck (by simp) h)
      | transition =>
          exact False.elim (hstuck (by simp) h)
      | blank =>
          exact False.elim (hstuck (by simp) h)
      | zero =>
          exact False.elim (hstuck (by simp) h)
      | one =>
          exact False.elim (hstuck (by simp) h)
      | moveLeft =>
          exact False.elim (hstuck (by simp) h)
      | moveRight =>
          exact False.elim (hstuck (by simp) h)



end Computability
end FoC
