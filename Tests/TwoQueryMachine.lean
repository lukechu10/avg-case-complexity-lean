import AverageCaseComplexity.Reductions.TwoQueryMachine
import AverageCaseComplexity.Reductions.StateReindex

open AverageCaseComplexity AverageCaseComplexity.OracleMachine

-- These include actual finite-control transformations, complete trace semantics,
-- clock padding after genuine halting, and the general two-query construction.
run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``runFrom_add, ``runFrom_eq_of_halted, ``runFrom_writeQuery,
      ``runFrom_seq, ``runFrom_ask, ``runFrom_agree, ``run_twoQuery,
      ``exists_twoQuery_machine, ``runFrom_reindex, ``run_reindex] do
    let axioms ← Lean.collectAxioms decl
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{decl} depends on unexpected axiom {axiomName}"
