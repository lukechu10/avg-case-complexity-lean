module

public import AverageCaseComplexity.Amplification.Flat.Bounds
public import AverageCaseComplexity.Amplification.ErrorBounds

@[expose] public section

namespace AverageCaseComplexity

/-- Linear repetition gives a strictly exponentially small probability for every
initially rare answer. The rate is fixed independently of the input. -/
theorem flatPMF_exponential_lt (p : PMF Answer) (a : Answer) (rate n count : ℕ)
    (hmass : p a ≤ (1/4 : ENNReal))
    (hcount : 72 * (rate + 1) * (n + 1) ≤ count) :
    flatPMF p count a < exponentialError rate n := by
  have hcountpos : 0 < count := by
    have : 0 < 72 * (rate + 1) * (n + 1) := by positivity
    omega
  have hr := (ENNReal.toReal_le_toReal (p.apply_ne_top a) (by norm_num)).mpr hmass
  norm_num at hr
  have htail := flatPMF_rare_le p a count hcountpos hr
  have hreal : (72 : ℝ) * ((rate : ℝ) + 1) * ((n : ℝ) + 1) ≤ (count : ℝ) := by
    exact_mod_cast hcount
  have hexponent : -(count : ℝ) / 72 < -(rate : ℝ) * ((n : ℝ) + 1) := by
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n,
      show (0 : ℝ) ≤ rate from Nat.cast_nonneg rate]
  apply (ENNReal.toReal_lt_toReal ((flatPMF p count).apply_ne_top a)
    ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using
    htail.trans_lt (Real.exp_lt_exp.mpr hexponent)

end AverageCaseComplexity
