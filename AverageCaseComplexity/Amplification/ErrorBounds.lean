module

public import AverageCaseComplexity.Schemes
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Length-dependent internal error thresholds

The internal error depends on input length, whereas the outer exceptional-input
mass remains strictly below the requested reciprocal accuracy `1/k`.
-/

namespace AverageCaseComplexity

/-- Errorless guarantees with a possibly length-dependent internal threshold. -/
structure LengthErrorlessConditions (error : ℕ → ENNReal) (A : RandomizedScheme)
    (P : DistributionalProblem) : Prop where
  correct : ∀ k x, P.distribution.Supports x →
    wrongProb P.language x (A x k) < error x.length
  useful : ∀ k n, P.distribution.prob n
    (fun x => error n ≤ A x k none) < k.bound

/-- Exponentially small internal error; positive `rate` gives exponential decay.
The shift by one supplies a nonzero size parameter even on the empty input. -/
noncomputable def exponentialError (rate n : ℕ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(rate : ℝ) * ((n : ℝ) + 1)))

@[simp] theorem exponentialError_pos (rate n : ℕ) : 0 < exponentialError rate n := by
  simp [exponentialError, Real.exp_pos]

/-- Rates at least two give a threshold strictly below the original `1/4`,
including at input length zero. -/
theorem exponentialError_lt_quarter (rate n : ℕ) (hrate : 2 ≤ rate) :
    exponentialError rate n < (1/4 : ENNReal) := by
  have he : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have he2 : (4 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hsmall : Real.exp (-2 : ℝ) < 1/4 := by
    rw [Real.exp_neg]
    apply (inv_lt_iff_one_lt_mul₀ (Real.exp_pos (2 : ℝ))).mpr
    nlinarith
  have hrate' : (2 : ℝ) ≤ rate := by exact_mod_cast hrate
  have hlarge : (2 : ℝ) ≤ (rate : ℝ) * ((n : ℝ) + 1) := by
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hreal : Real.exp (-(rate : ℝ) * ((n : ℝ) + 1)) < 1/4 :=
    (Real.exp_le_exp.mpr (by nlinarith)).trans_lt hsmall
  have h := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1/4)).mpr hreal
  simpa [exponentialError] using h

/-- Relaxing an internal threshold preserves both kinds of errorless guarantees. -/
theorem LengthErrorlessConditions.mono {error error' : ℕ → ENNReal}
    {A : RandomizedScheme} {P : DistributionalProblem}
    (h : LengthErrorlessConditions error A P) (hle : ∀ n, error n ≤ error' n) :
    LengthErrorlessConditions error' A P := by
  constructor
  · intro k x hx
    exact (h.correct k x hx).trans_le (hle x.length)
  · intro k n
    apply lt_of_le_of_lt (P.distribution.prob_mono_on_support n ?_) (h.useful k n)
    intro x _ hx
    exact (hle n).trans hx

/-- A length-dependent bound at most `1/4` implies the original scheme conditions. -/
theorem LengthErrorlessConditions.toErrorlessConditions {error : ℕ → ENNReal}
    {A : RandomizedScheme} {P : DistributionalProblem}
    (h : LengthErrorlessConditions error A P) (hle : ∀ n, error n ≤ (1/4 : ENNReal)) :
    A.ErrorlessConditions P := by
  constructor
  · intro k x hx
    exact (h.correct k x hx).trans_le (hle x.length)
  · intro k n
    apply lt_of_le_of_lt (P.distribution.prob_mono_on_support n ?_) (h.useful k n)
    intro x _ hx
    exact (hle n).trans hx

end AverageCaseComplexity
