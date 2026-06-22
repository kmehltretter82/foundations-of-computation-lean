import FoC.Book.Chapter05.Section03.BasicPart1

set_option doc.verso true

/-!
# Section 5.3: Basic Definitions (Part 2)

This module provides the second part of the supporting declarations and
helper lemmas for Section 5.3. It connects the abstract universal machine
mechanics with concrete encoded representations and pair-halting arguments.
-/
namespace FoC
namespace Book
namespace Chapter05
namespace Section03
open Languages
open Computability

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

theorem decidable_preimage_construction_of_faithful_computable_map_construction
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction input output)
    {map : Word input -> Word output}
    (hcomputable : FaithfulTuringComputableWordMap map) :
    TuringDecidablePreimageConstruction map :=
  Computability.decidablePreimagePrinciple_of_faithfulComputableMapPrinciple
    hpreimage hcomputable

theorem faithful_computable_map_decidable_preimage_construction_of_computable_map_construction
    (hpreimage : ComputableMapDecidablePreimageConstruction input output) :
    FaithfulComputableMapDecidablePreimageConstruction input output :=
  Computability.faithfulComputableMapDecidablePreimagePrinciple_of_computableMapPrinciple
    hpreimage

theorem diagonal_pair_decidable_preimage_construction_of_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage : ComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable : TuringComputableWordMap (TuringDiagonalPairMap encodePair)) :
    DiagonalPairDecidablePreimageConstruction encodePair :=
  Computability.diagonalPairDecidablePreimagePrinciple_of_computableMapPrinciple
    hinj hpreimage hcomputable

theorem diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable :
      FaithfulTuringComputableWordMap (TuringDiagonalPairMap encodePair)) :
    DiagonalPairDecidablePreimageConstruction encodePair :=
  Computability.diagonalPairDecidablePreimagePrinciple_of_faithfulComputableMapPrinciple
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

theorem diagonal_pair_decidable_reduction_self_halting_to_pair_halting_of_faithful_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable :
      FaithfulTuringComputableWordMap (TuringDiagonalPairMap encodePair))
    {haltsOnCodeInput : Word code -> Word code -> Prop} :
    TuringDecidableReduction
      (TuringSelfHaltingLanguage haltsOnCodeInput)
      (TuringPairHaltingProblem encodePair haltsOnCodeInput) :=
  diagonal_pair_decidable_reduction_self_halting_to_pair_halting
    (diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
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

theorem concrete_diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : FaithfulConcreteDiagonalPairMapComputable) :
    DiagonalPairDecidablePreimageConstruction
      (ConcretePairEncoding :
        Word ConcreteMachineCodeSymbol ->
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) := by
  simpa [DiagonalPairDecidablePreimageConstruction,
    ConcretePairEncoding, ConcretePairCodeSymbol, ConcreteDiagonalPairMap,
    FaithfulConcreteDiagonalPairMapComputable,
    FaithfulComputableMapDecidablePreimageConstruction,
    FaithfulTuringComputableWordMap]
    using
      PairCodeSymbol.diagonalPairDecidablePreimagePrinciple_of_concrete_faithful_computable_map
        (code := ConcreteMachineCodeSymbol) hpreimage hcomputable

theorem concrete_diagonal_pair_decidable_preimage_construction_of_faithful_preimage
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) :
    DiagonalPairDecidablePreimageConstruction
      (ConcretePairEncoding :
        Word ConcreteMachineCodeSymbol ->
          Word ConcreteMachineCodeSymbol ->
            Word (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) :=
  concrete_diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
    hpreimage faithful_concrete_diagonal_pair_map_computable

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

theorem concrete_machine_self_halting_reduces_to_pair_halting_of_faithful_computable_map
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : FaithfulConcreteDiagonalPairMapComputable) :
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
        (concrete_diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
          hpreimage hcomputable)

theorem concrete_machine_self_halting_reduces_to_pair_halting_of_faithful_preimage
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol)) :
    TuringDecidableReduction
      ConcreteMachineSelfHaltingLanguage
      ConcreteMachinePairHaltingProblem :=
  concrete_machine_self_halting_reduces_to_pair_halting_of_faithful_computable_map
    hpreimage faithful_concrete_diagonal_pair_map_computable

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

set_option doc.verso true

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

theorem pair_halting_undecidable_if_decoder_universal_of_faithful_computable_map
    {encodePair : Word code -> Word code -> Word pairSymbol}
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hinj : TuringPairEncodingInjective encodePair)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction code pairSymbol)
    (hcomputable :
      FaithfulTuringComputableWordMap (TuringDiagonalPairMap encodePair))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem encodePair decodeAccepts) :=
  Computability.pairHalting_undecidable_if_decoder_universal
    haccept
    (diagonal_pair_decidable_preimage_construction_of_faithful_computable_map
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

theorem concrete_pair_halting_undecidable_if_decoder_universal_of_faithful_computable_map
    {decodeAccepts : Word code -> Word code -> Prop}
    (haccept : DecidableToAcceptableConstruction code)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction code
        (ConcretePairCodeSymbol code))
    (hcomputable :
      FaithfulTuringComputableWordMap
        (ConcreteDiagonalPairMap :
          Word code -> Word (ConcretePairCodeSymbol code)))
    (huniv : TuringDecoderUniversalForAcceptableLanguages decodeAccepts) :
    UndecidableTuringLanguage
      (TuringPairHaltingProblem
        (ConcretePairEncoding :
          Word code -> Word code -> Word (ConcretePairCodeSymbol code))
        decodeAccepts) :=
  PairCodeSymbol.concretePairHalting_undecidable_if_decoder_universal_of_faithful_computable_map
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

theorem concrete_machine_pair_halting_undecidable_if_self_halting_undecidable_of_faithful_computable_map
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : FaithfulConcreteDiagonalPairMapComputable)
    (hself :
      UndecidableTuringLanguage ConcreteMachineSelfHaltingLanguage) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem :=
  undecidable_of_decidable_reduction
    (concrete_machine_self_halting_reduces_to_pair_halting_of_faithful_computable_map
      hpreimage hcomputable)
    hself

theorem concrete_machine_pair_halting_undecidable_if_self_halting_undecidable_of_faithful_preimage
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hself :
      UndecidableTuringLanguage ConcreteMachineSelfHaltingLanguage) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem :=
  concrete_machine_pair_halting_undecidable_if_self_halting_undecidable_of_faithful_computable_map
    hpreimage faithful_concrete_diagonal_pair_map_computable hself

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

theorem concrete_machine_pair_halting_undecidable_if_decoder_universal_of_faithful_computable_map
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcomputable : FaithfulConcreteDiagonalPairMapComputable)
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem := by
  simpa [ConcreteMachinePairHaltingProblem]
    using
      concrete_pair_halting_undecidable_if_decoder_universal_of_faithful_computable_map
        (code := ConcreteMachineCodeSymbol)
        (decodeAccepts := ConcreteMachineCodeAccepts)
        haccept hpreimage hcomputable huniv

theorem concrete_machine_pair_halting_undecidable_if_decoder_universal_of_faithful_preimage
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (huniv : ConcreteMachineDecoderUniversalForAcceptableLanguages) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem :=
  concrete_machine_pair_halting_undecidable_if_decoder_universal_of_faithful_computable_map
    haccept hpreimage faithful_concrete_diagonal_pair_map_computable huniv

theorem concrete_machine_pair_halting_undecidable_if_encoded_input_compiler_of_faithful_preimage
    (haccept :
      DecidableToAcceptableConstruction ConcreteMachineCodeSymbol)
    (hpreimage :
      FaithfulComputableMapDecidablePreimageConstruction
        ConcreteMachineCodeSymbol
        (ConcretePairCodeSymbol ConcreteMachineCodeSymbol))
    (hcompile : ConcreteEncodedInputDescriptionCompilerConstruction) :
    UndecidableTuringLanguage ConcreteMachinePairHaltingProblem :=
  concrete_machine_pair_halting_undecidable_if_decoder_universal_of_faithful_preimage
    haccept hpreimage
    (concrete_encoded_input_description_compiler_decoder_universal hcompile)

/-!
The abstract row-coverage lemmas below are parameterized by an arbitrary
decoder relation.  The concrete construction that follows instantiates the
universal-machine target with the prefix specification, where the runner
decodes one self-delimiting machine description from the front of the tape and
uses the remaining symbols as the simulated input.
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

theorem concrete_universal_prefix_machine_halts_on_encoded_description_iff
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalPrefixMachineSpec universal)
    (D : ConcreteMachineDescription)
    (input : Word ConcreteMachineCodeSymbol) :
    TuringMachine.HaltsOnInput universal
      (Languages.Word.Concat (ConcreteMachineEncode D) input) <->
        ConcreteMachineHaltsOnInput D
          (ConcreteMachineEncodeCodeInput input) :=
  Computability.codeUniversalPrefixMachine_halts_on_encoded_description_iff
    hspec D input

theorem concrete_universal_prefix_machine_row_language_equal_encoded_input_language
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalPrefixMachineSpec universal)
    (D : ConcreteMachineDescription) :
    Language.Equal
      (UniversalMachineRowLanguage universal (ConcreteMachineEncode D))
      (ConcreteMachineEncodedInputLanguage D) :=
  Computability.codeUniversalPrefixMachine_rowLanguage_equal_encodedInputLanguage
    hspec D

theorem concrete_universal_prefix_machine_rows_cover_of_encoded_input_description_compiler
    {universal : TuringMachine ConcreteMachineCodeSymbol state}
    (hspec : ConcreteUniversalPrefixMachineSpec universal)
    (hcompile : ConcreteEncodedInputDescriptionCompilerConstruction) :
    ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  Computability.codeUniversalPrefixRowsCoverAcceptableLanguages_of_encodedInputDescriptionCompiler
    hspec hcompile

theorem exists_concrete_universal_prefix_machine_rows_cover_of_constructions
    (hcompile : ConcreteEncodedInputDescriptionCompilerConstruction)
    (hrunner : ConcreteUniversalPrefixRunnerConstruction) :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal ∧
          ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  Computability.codeUniversalPrefixRowsCoverConstruction_of_constructions
    hcompile hrunner

theorem exists_concrete_universal_prefix_machine_rows_cover_of_section53_closeout
    (hclose : ConcreteSection53UniversalPrefixCloseout) :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal ∧
          ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  Computability.codeUniversalPrefixRowsCoverConstruction_of_section53Closeout
    hclose

theorem exists_concrete_universal_prefix_machine_rows_cover_of_finite_source_closeout
    (hclose : ConcreteSection53UniversalPrefixFiniteSourceCloseout) :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal ∧
          ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  Computability.codeUniversalPrefixRowsCoverConstruction_of_finiteSourceCloseout
    hclose

/-!
**Section 5.3 scaffold.**  The universal-machine target is the prefix runner
route.  These wrappers expose the reusable finite-source runner scaffold at the
book-facing layer.  Row coverage remains available through the closeout theorem
above when an explicit encoded-input description compiler is supplied.
-/

theorem concrete_code_prefix_recognizer_machine_scaffold :
    ConcreteCodePrefixRecognizerMachineConstruction :=
  Computability.codePrefixRecognizerMachineConstruction_scaffold

def concrete_section53_universal_prefix_runner_finite_source_closeout_scaffold :
    ConcreteSection53UniversalPrefixRunnerFiniteSourceCloseout :=
  Computability.codeUniversalPrefixRunnerFiniteSourceCloseout_scaffold

theorem concrete_universal_prefix_runner_scaffold :
    ConcreteUniversalPrefixRunnerConstruction :=
  Computability.codeUniversalPrefixRunnerConstruction_scaffold

theorem exists_concrete_universal_prefix_machine_scaffold :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal :=
  concrete_universal_prefix_runner_scaffold

theorem exists_concrete_universal_prefix_machine_rows_cover_of_boolean_description_compiler
    (hcompiler : ConcreteBooleanDescriptionAcceptorCompilationConstruction)
    (hrunner : ConcreteCodePrefixRecognizerMachineConstruction) :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal ∧
          ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  exists_concrete_universal_prefix_machine_rows_cover_of_finite_source_closeout
    (concrete_section53_universal_prefix_finite_source_closeout_of_boolean_description_compiler
      hcompiler hrunner)

theorem exists_concrete_universal_prefix_machine_rows_cover_of_program_compiler_and_runner
    (hcompiler : ConcreteEncodedInputProgramAcceptorCompilationConstruction)
    (hrunner : ConcreteUniversalPrefixRunnerConstruction) :
    exists state : Type,
      exists universal : TuringMachine ConcreteMachineCodeSymbol state,
        ConcreteUniversalPrefixMachineSpec universal ∧
          ConcreteUniversalPrefixMachineRowsCoverAcceptableLanguages universal :=
  exists_concrete_universal_prefix_machine_rows_cover_of_section53_closeout
    (concrete_section53_universal_prefix_closeout_of_constructions
      hcompiler hrunner)

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
finite tape-window artifacts. The concrete diagonal pair map now has a faithful
finite-machine witness, and the concrete theorem wrappers reuse that witness
without asking callers to pass it again.

The viable universal-machine target is the prefix version. The semantic staged
recognizer {name}`ConcreteCodePrefixRecognizerProgram` accepts exactly
{name}`ConcreteMachineCodePrefixAcceptedLanguage`. The encoded-input compiler
handoff now factors through
{name}`ConcreteBooleanDescriptionAcceptorCompilationConstruction`: Boolean
inputs are decoded by {name}`MachineDescription.decodeCodeWordAsInput`, and
canonical inputs produced by {name}`MachineDescription.encodeCodeWordAsInput`
recover the original code-symbol recognizer. Thus row-coverage closeouts can
reuse an explicit Boolean description compiler instead of carrying a separate
encoded-input program compiler. The remaining fixed-alphabet runner work is
now isolated as
{name}`ConcreteCodePrefixRecognizerMachineConstruction`; this target is
equivalent to {name}`ConcreteUniversalPrefixRunnerConstruction`, because the
prefix recognizer's language is exactly the decoder relation needed by the
universal machine. The prefix parser layer is now formalized as
{name}`ConcreteCodePrefixParserCodeConstruction`: a normalizing code primitive
succeeds exactly on one-description prefixes, and a total branch primitive
emits the success or failure code used by the later recognizer controller. The
no-argument scaffold records this runner target as the active deferred
construction. For row coverage, the explicit
{name}`ConcreteSection53UniversalPrefixFiniteSourceCloseout` pairs that runner
target with an encoded-input description compiler and routes directly to
{name}`exists_concrete_universal_prefix_machine_rows_cover_of_finite_source_closeout`.
This is the same finite-source layer used by Section 5.2: canonical
{name}`MachineCodeSymbol` parsers, normalized-output emitters,
subroutine-ready sequencing, and cell or parse branch controllers. Together
with the explicit compiler assumption, the closeout fields imply row coverage
by the finite-source closeout theorem, while the older program-compiler route
remains as a compatibility wrapper.
-/

end Section03
end Chapter05
end Book
end FoC
