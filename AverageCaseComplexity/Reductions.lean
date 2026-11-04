module

public import AverageCaseComplexity.Reductions.Definitions
public import AverageCaseComplexity.Reductions.Closure

/-!
# Deterministic distributional Turing reductions

Oracle-machine execution, Definition 2.2, and machine-certified heuristic
closure. Errorless closure explicitly requires support-preserving queries;
the paper's exceptional-set domination condition alone does not establish
the pointwise correctness of its proposed simulation.
-/
