import AverageCaseComplexity.Completeness.TwoQuery
import AverageCaseComplexity.Completeness.FairTables
import AverageCaseComplexity.Completeness.SourceReplay
import AverageCaseComplexity.Completeness.TupleDecodingRuntime
import Lean

open AverageCaseComplexity AverageCaseComplexity.Completeness.TwoQuery

-- These are unconditional milestones even while runtime certification is pending.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``exactLanguageBit_eq, ``reliabilityTest_accept_lower,
      ``reliabilityTest_accept_upper, ``sampler_eval, ``sampler_output_length,
      ``distribution_mass_lower, ``distribution_mass_upper, ``exactBranchTest_efficient,
      ``targetProgram_correct, ``targetProgram_useful, ``CompiledSource.reduction_trace,
      ``CompiledSource.reduction_run, ``run_coinDesc, ``specialize_clocked_source,
      ``replay_clocked_sampler, ``rawCompiler_correct, ``compile_algorithm, ``compile_sampler,
      ``decodeSD_efficient, ``decodeSeed_efficient, ``decode_efficient] do
    for axiomName in ← Lean.collectAxioms decl do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {decl}"
