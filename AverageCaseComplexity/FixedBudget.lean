module

public import AverageCaseComplexity.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Fixed-budget algorithms (Section 2.4)

Unlike schemes, these algorithms take no accuracy argument. The deterministic
errorless condition is global correctness-or-give-up, exactly as stated for
fixed-budget algorithms in Section 2.4 (not the support-restricted AvgP condition).
-/

@[expose] public section

namespace AverageCaseComplexity

open Turing.MultiTapeTM

abbrev FixedAlgorithm := Word → Answer

/-- A fixed-input deterministic algorithm with a real tidy machine certificate. -/
structure PolyTimeDeterministicAlgorithm where
  run : FixedAlgorithm
  efficient : ComputableTidilyInPolyTime run encBits answerEncoding

namespace FixedAlgorithm

def HeuristicConditions (A : FixedAlgorithm) (P : DistributionalProblem) (η : ℕ → ENNReal) : Prop :=
  ∀ n, P.distribution.prob n (fun x => A x ≠ some (P.language x)) < η n

structure ErrorlessConditions (A : FixedAlgorithm) (P : DistributionalProblem) (η : ℕ → ENNReal) : Prop where
  correct : ∀ x, IsAllowed P.language x (A x)
  useful : ∀ n, P.distribution.prob n (fun x => A x = none) < η n

theorem ErrorlessConditions.toHeuristic {A : FixedAlgorithm} {P : DistributionalProblem}
    {η : ℕ → ENNReal} (h : A.ErrorlessConditions P η) : A.HeuristicConditions P η := by
  intro n
  apply lt_of_le_of_lt (P.distribution.prob_mono_on_support n ?_) (h.useful n)
  intro x hx hfail
  rcases h.correct x with hcorrect | hnone
  · exact False.elim (hfail hcorrect)
  · exact hnone

end FixedAlgorithm

/-- The paper's `Heur_η P`. -/
def HeurFixedP (η : ℕ → ENNReal) (P : DistributionalProblem) : Prop :=
  ∃ A : PolyTimeDeterministicAlgorithm, A.run.HeuristicConditions P η

/-- The paper's `Avg_η P`, with its global errorlessness requirement. -/
def AvgFixedP (η : ℕ → ENNReal) (P : DistributionalProblem) : Prop :=
  ∃ A : PolyTimeDeterministicAlgorithm, A.run.ErrorlessConditions P η

theorem AvgFixedP.toHeurFixedP {η : ℕ → ENNReal} {P : DistributionalProblem}
    (h : AvgFixedP η P) : HeurFixedP η P := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, hA.toHeuristic⟩

/-- Natural-exponent specialization; arbitrary error budgets also allow real
exponents. At length zero this is ENNReal infinity when `c > 0`. -/
noncomputable def inversePolynomialError (c n : ℕ) : ENNReal := ((n : ENNReal) ^ c)⁻¹

theorem inversePolynomialError_le_bound {c n : ℕ} {j : Accuracy}
    (h : j.val ≤ n ^ c) : inversePolynomialError c n ≤ j.bound := by
  apply ENNReal.inv_le_inv.mpr
  exact_mod_cast h

/-- Real-exponent inverse-power error, covering the paper's arbitrary positive
constant `c` rather than just natural exponents. -/
noncomputable def inversePowerError (c : ℝ) (n : ℕ) : ENNReal := ((n : ENNReal) ^ c)⁻¹

theorem inversePowerError_le_bound {c : ℝ} {n : ℕ} {j : Accuracy}
    (h : (j.val : ENNReal) ≤ (n : ENNReal) ^ c) : inversePowerError c n ≤ j.bound :=
  ENNReal.inv_le_inv.mpr h

@[simp] theorem inversePowerError_natCast (c n : ℕ) :
    inversePowerError (c : ℝ) n = inversePolynomialError c n := by
  simp [inversePowerError, inversePolynomialError]

end AverageCaseComplexity
