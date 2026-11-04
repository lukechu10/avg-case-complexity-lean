module

public import AverageCaseComplexity.FixedBudget
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO

/-!
# Explicit deterministic time bounds

Every effectiveness field below is backed by an actual tidy machine certificate.
The one-variable classes use encoded input size `n+k+2`, consistently with the
project's accuracy convention. Polynomial equivalence with `nk` does not imply
equivalence of arbitrary time functions: no such equivalence is claimed.
-/

@[expose] public section

namespace AverageCaseComplexity

open Turing.MultiTapeTM

/-- A deterministic scheme with a specified (possibly nonpolynomial) input-wise
bound. Its executable implementation is supplied by `ComputableTidilyInO`. -/
structure TimeBoundedDeterministicScheme (time : Word × Accuracy → ℕ) where
  run : DeterministicScheme
  efficient : ComputableTidilyInO (fun a : Word × Accuracy => run a.1 a.2)
    schemeInputEncoding answerEncoding time time

/-- Input-wise time class, before specializing the time function to input size. -/
def AvgTimeWithBound (time : Word × Accuracy → ℕ) (P : DistributionalProblem) : Prop :=
  ∃ A : TimeBoundedDeterministicScheme time, A.run.ErrorlessConditions P

def HeurTimeWithBound (time : Word × Accuracy → ℕ) (P : DistributionalProblem) : Prop :=
  ∃ A : TimeBoundedDeterministicScheme time, A.run.HeuristicConditions P

/-- Scheme time `O(g(n+k+2))`, measured in the actual encoded input size plus one. -/
def AvgTime (g : ℕ → ℕ) : DistributionalProblem → Prop :=
  AvgTimeWithBound (fun a => g ((schemeInputEncoding a).length + 1))

def HeurTime (g : ℕ → ℕ) : DistributionalProblem → Prop :=
  HeurTimeWithBound (fun a => g ((schemeInputEncoding a).length + 1))

/-- Deterministic average exponential time, using positive natural exponents. -/
def AvgEXP (P : DistributionalProblem) : Prop :=
  ∃ c : ℕ, 0 < c ∧ AvgTime (fun n => 2 ^ (n ^ c)) P

/-- A fixed-budget algorithm with runtime `O(g(|x|))`. -/
structure TimeBoundedDeterministicAlgorithm (g : ℕ → ℕ) where
  run : FixedAlgorithm
  efficient : ComputableTidilyInO run encBits answerEncoding
    (fun x => g x.length) (fun x => g x.length)

def AvgFixedTime (η : ℕ → ENNReal) (g : ℕ → ℕ) (P : DistributionalProblem) : Prop :=
  ∃ A : TimeBoundedDeterministicAlgorithm g, A.run.ErrorlessConditions P η

def HeurFixedTime (η : ℕ → ENNReal) (g : ℕ → ℕ) (P : DistributionalProblem) : Prop :=
  ∃ A : TimeBoundedDeterministicAlgorithm g, A.run.HeuristicConditions P η

theorem AvgTimeWithBound.toHeurTimeWithBound {time : Word × Accuracy → ℕ}
    {P : DistributionalProblem} (h : AvgTimeWithBound time P) : HeurTimeWithBound time P := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, hA.toHeuristic⟩

theorem AvgFixedTime.toHeurFixedTime {η : ℕ → ENNReal} {g : ℕ → ℕ}
    {P : DistributionalProblem} (h : AvgFixedTime η g P) : HeurFixedTime η g P := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, hA.toHeuristic⟩

end AverageCaseComplexity
