module

public import AverageCaseComplexity.Reductions.Definitions
public import AverageCaseComplexity.Reductions.Closure
public import AverageCaseComplexity.Reductions.Corollaries

/-!
# Deterministic distributional Turing reductions

Oracle-machine execution, Definition 2.2, machine-certified heuristic closure,
fixed-budget closure (Corollary 2.1), and quantitative cutoff substitution
(Corollary 2.2 with an explicit target-cost envelope).

General errorless substitution retains an explicit support-preservation or
global-target-correctness qualification. Fixed-budget errorless algorithms
are globally correct by definition, so Corollary 2.1 needs no support repair.
Arbitrary target time is not assumed to absorb polynomial argument inflation.
-/
