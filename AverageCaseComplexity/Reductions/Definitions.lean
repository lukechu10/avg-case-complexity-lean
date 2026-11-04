module

public import AverageCaseComplexity.Distributions.WordMass
public import AverageCaseComplexity.Reductions.OracleScheme

@[expose] public section

/-!
# Distributional deterministic Turing reductions (Itsykson Definition 2.2)

We use the uniformly halting machine convention of `OracleScheme`, stronger
than the paper's displayed target-only effectiveness condition; equivalence
of these runtime conventions is not established here.

The oracle is the exact characteristic function of the target language.
One polynomial domination factor works for all lengths and accuracies. At each
length/accuracy, a single exceptional set works simultaneously for all queries.
Its mass bound is non-strict, unlike the strict usefulness/error bounds.

We use `n + k + 2`, the encoded-input length plus one, as polynomial size
parameter. For positive `n` this is polynomially equivalent to the paper's
`n/δ = n*k`. It also defines meaningful bounds at length zero.
-/

namespace AverageCaseComplexity

namespace PolyTimeOracleScheme

/-- Source mass of non-exceptional inputs which query `y` at least once.
Repeated occurrences do not contribute additional mass. -/
noncomputable def queryMass (T : PolyTimeOracleScheme) (L : Language) (D : Ensemble)
    (k : Accuracy) (n : ℕ) (exceptional : Set (FixedWord n)) (y : Word) : ENNReal :=
  eventProb (D n) (fun x => x ∉ exceptional ∧ T.Asks L x.toWord k y)

open scoped Classical in
/-- The event formulation is exactly the paper's indicator-weighted finite sum. -/
theorem queryMass_eq_sum (T : PolyTimeOracleScheme) (L : Language) (D : Ensemble)
    (k : Accuracy) (n : ℕ) (exceptional : Set (FixedWord n)) (y : Word) :
    T.queryMass L D k n exceptional y =
      ∑ x : FixedWord n, if x ∉ exceptional then
        (T.askIndicator L x.toWord k y : ENNReal) * D n x else 0 := by
  classical
  unfold queryMass eventProb
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : x ∈ exceptional <;> by_cases ha : T.Asks L x.toWord k y <;>
    simp [he, ha, askIndicator]

/-- A single natural polynomial majorant, evaluated on the encoded input size. -/
def dominationFactor (coefficient degree n : ℕ) (k : Accuracy) : ℕ :=
  coefficient * (n + k.val + 2) ^ degree

/-- Domination under the true target oracle. `exceptional` may depend on `n,k`,
but not on the query word `y`. No normalization across different query lengths
is imposed on the target ensemble. -/
def Domination (T : PolyTimeOracleScheme) (source target : DistributionalProblem) : Prop :=
  ∃ coefficient degree : ℕ, ∀ (k : Accuracy) (n : ℕ),
    ∃ exceptional : Set (FixedWord n),
      eventProb (source.distribution n) exceptional ≤ k.bound ∧
      ∀ y : Word, T.queryMass target.language source.distribution k n exceptional y ≤
        (dominationFactor coefficient degree n k : ENNReal) * target.distribution.wordMass y

end PolyTimeOracleScheme

/-- The non-runtime conditions of an errorless distributional Turing reduction.
Effectiveness is already part of the machine-certified scheme `T`. -/
structure ErrorlessReductionConditions (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) : Prop where
  errorless : (T.run target.language).ErrorlessConditions source
  domination : T.Domination source target

/-- The heuristic variant removes pointwise correctness and bounds total failure,
including give-up, on the source input distribution. -/
structure HeuristicReductionConditions (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) : Prop where
  heuristic : (T.run target.language).HeuristicConditions source
  domination : T.Domination source target

/-- Errorless distributional deterministic Turing reducibility, with the uniform
oracle-halting certificate documented above. -/
def ErrorlesslyReducible (source target : DistributionalProblem) : Prop :=
  ∃ T : PolyTimeOracleScheme, ErrorlessReductionConditions T source target

/-- Heuristic distributional deterministic Turing reducibility, with the same
uniform oracle-halting convention. -/
def HeuristicallyReducible (source target : DistributionalProblem) : Prop :=
  ∃ T : PolyTimeOracleScheme, HeuristicReductionConditions T source target

end AverageCaseComplexity
