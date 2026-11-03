module

public import AverageCaseComplexity.Amplification.Flat.Exponential
public import AverageCaseComplexity.Amplification.Flat.Runtime

@[expose] public section

/-!
# Efficient exponential-error amplification

For each fixed natural rate, flat repetition produces internal error less than
`exp(-rate * (n+1))`, while preserving the outer exceptional-input mass `< 1/k`.
The number of base executions is linear in the complete encoded input length.
This proves the downward-amplification direction of Itsykson's Lemma 2.1.
-/

namespace AverageCaseComplexity

/-- The encoded-length repetition clock is sufficient for a length-only error bound. -/
theorem linearRepeatCount_ge (rate : ℕ) (x : Word) (k : Accuracy) :
    72 * (rate + 1) * (x.length + 1) ≤ linearRepeatCount rate (x, k) := by
  have hl : x.length + 1 ≤ (schemeInputEncoding (x, k)).length + 1 := by
    simp only [schemeInputEncoding, Function.Embedding.coeFn_mk, encodeSchemeInput_length]
    omega
  exact Nat.mul_le_mul_left _ hl

/-- Polynomial-time amplification to an exponentially small length-dependent threshold.
For positive `rate`, the threshold decays exponentially in input length.
The machine, its polynomial clock, and the rate are uniform over inputs and accuracies. -/
theorem amplification_exponential (A : PolyTimeRandomizedScheme) (P : DistributionalProblem)
    (h : A.run.ErrorlessConditions P) (rate : ℕ) :
    LengthErrorlessConditions (exponentialError rate) (A.flatAmplifyLinear rate).run P := by
  constructor
  · intro k x hx
    rw [wrongProb_eq_mass, run_flatAmplifyLinear]
    apply flatPMF_exponential_lt
    · exact le_of_lt (by simpa only [wrongProb_eq_mass] using h.correct k x hx)
    · exact linearRepeatCount_ge rate x k
  · intro k n
    apply lt_of_le_of_lt (P.distribution.prob_mono_on_length n ?_) (h.useful k n)
    intro x hlen _ hnew
    by_contra hold
    have hsmall := flatPMF_exponential_lt (A.run x k) none rate x.length
      (linearRepeatCount rate (x, k)) (le_of_lt (lt_of_not_ge hold))
      (linearRepeatCount_ge rate x k)
    rw [run_flatAmplifyLinear] at hnew
    rw [hlen] at hsmall
    exact (not_lt_of_ge hnew) hsmall

/-- Any requested length-dependent threshold bounded below by an exponential
is achievable by a certified polynomial-time scheme. The target function itself
need not be read or computed by the scheme; a fixed dominating rate suffices. -/
theorem amplification_for_thresholds (A : PolyTimeRandomizedScheme)
    (P : DistributionalProblem) (h : A.run.ErrorlessConditions P)
    (error : ℕ → ENNReal) (rate : ℕ) (hlower : ∀ n, exponentialError rate n ≤ error n) :
    ∃ B : PolyTimeRandomizedScheme, LengthErrorlessConditions error B.run P :=
  ⟨A.flatAmplifyLinear rate, (amplification_exponential A P h rate).mono hlower⟩

/-- For every rate at least two, exponential-error schemes characterize exactly
`AvgBPP`. This includes both the effective amplification and the easy reverse inclusion. -/
theorem avgBPP_iff_exponential (P : DistributionalProblem) (rate : ℕ) (hrate : 2 ≤ rate) :
    AvgBPP P ↔ ∃ B : PolyTimeRandomizedScheme,
      LengthErrorlessConditions (exponentialError rate) B.run P := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A.flatAmplifyLinear rate, amplification_exponential A P hA rate⟩
  · rintro ⟨B, hB⟩
    exact ⟨B, hB.toErrorlessConditions (fun n => (exponentialError_lt_quarter rate n hrate).le)⟩

end AverageCaseComplexity
