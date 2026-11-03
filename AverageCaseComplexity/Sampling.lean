module

public import AverageCaseComplexity.Distributions
public import Complexity.Computability.Probabilistic.PPT

@[expose] public section

/-!
# Polynomial-time samplable ensembles

The sampler certificate uses Complexitylib's actual finite-control fair-coin
machine model. Its polynomial clock bounds every execution, not just expected
runtime. Samplability requires exact equality of output distributions.
-/

namespace AverageCaseComplexity

/-- Unary input encoding for the length parameter of a sampler. -/
def unaryEncoding : ℕ ↪ Word where
  toFun n := List.replicate n true
  inj' := by
    intro n m h
    simpa using congrArg List.length h

@[simp] theorem unaryEncoding_length (n : ℕ) : (unaryEncoding n).length = n := by
  simp [unaryEncoding]

/-- The word-valued distribution associated with the `n`th component. -/
noncomputable def Ensemble.wordDistribution (D : Ensemble) (n : ℕ) : PMF Word :=
  (D n).map FixedWord.toWord

/-- Itsykson's `PSamp`: exact sampling in strict polynomial time on unary input.

The executable program is accompanied by a uniform machine-level runtime
certificate; an arbitrary mathematical PMF is not an efficient sampler.
-/
def PSamp (D : Ensemble) : Prop :=
  ∃ S : ℕ → Cslib.ProbComp Word,
    Cslib.Probability.IsPPTOn unaryEncoding (Function.Embedding.refl Word) S ∧
    ∀ n, Cslib.ProbComp.eval (S n) = D.wordDistribution n

end AverageCaseComplexity
