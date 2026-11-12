module

public import AverageCaseComplexity.Completeness.AnswerLaw
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

/-- A conservative choice of the paper's N₀; only its inequalities matter. -/
def burnIn : ℕ := 10000

/-- The reliability test's two-sided tail allowance. -/
noncomputable def tailBound (n : ℕ) : ENNReal :=
  ENNReal.ofReal (2 * Real.exp (-((n : ℝ) ^ 2)))

theorem burnIn_tail :
    2 * Real.exp (-(burnIn : ℝ) / 1000) < (1 / 1000 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 10) 7
  norm_num [Finset.sum_range_succ] at h
  norm_num [burnIn, Real.exp_neg]
  change 2 / Real.exp 10 < (1 / 1000 : ℝ)
  apply (div_lt_iff₀ (Real.exp_pos 10)).mpr
  linarith

@[simp] theorem tailBound_pos (n : ℕ) : 0 < tailBound n := by
  exact ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) (Real.exp_pos _))

@[simp] theorem tailBound_ne_top (n : ℕ) : tailBound n ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- Larger encoded words have smaller reliability tails. -/
theorem tailBound_antitone : Antitone tailBound := by
  intro m n hmn
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have h : (m : ℝ) ≤ n := by exact_mod_cast hmn
  nlinarith [sq_nonneg ((n : ℝ) - m)]

/-- A deliberately coarse estimate, sufficient for the accepted-fraction
constant. Valid construction tuples are much longer than this minimum. -/
theorem tailBound_le_onePercent {n : ℕ} (hn : 15 ≤ n) :
    tailBound n ≤ (1 / 100 : ENNReal) := by
  have hn' : (15 : ℝ) ≤ n := by exact_mod_cast hn
  have he := Real.add_one_le_exp ((n : ℝ) ^ 2)
  have hexp : (200 : ℝ) ≤ Real.exp ((n : ℝ) ^ 2) := by nlinarith
  have hinv : (Real.exp ((n : ℝ) ^ 2))⁻¹ ≤ (200 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hexp
  have hreal : 2 * Real.exp (-((n : ℝ) ^ 2)) ≤ (1 / 100 : ℝ) := by
    rw [Real.exp_neg]
    linarith
  have h := ENNReal.ofReal_le_ofReal hreal
  norm_num only [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_one,
    ENNReal.ofReal_ofNat] at h
  exact h

theorem accepted_fraction_of_large {n : ℕ} (hn : 15 ≤ n) :
    (99 / 100 : ENNReal) ≤ 1 - tailBound n := by
  have h := tailBound_le_onePercent hn
  calc
    (99 / 100 : ENNReal) ≤ 1 - 1 / 100 := by
      apply ENNReal.le_sub_of_add_le_left (by finiteness)
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num
    _ ≤ 1 - tailBound n := tsub_le_tsub_left h 1

/-- Even after taking a union over all length-n words, the reliability
allowance is smaller than the inverse of their number. This is the numerical
estimate needed in the target solver's non-exact branch. -/
theorem binary_union_tail_lt {n : ℕ} (hn : 3 ≤ n) :
    (2 ^ n : ENNReal) * tailBound n < (2 ^ n : ENNReal)⁻¹ := by
  have htwo : (2 : ℝ) < Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 3
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hn2 : 2 * n + 1 ≤ n ^ 2 := by nlinarith
  have hnonzero : n ^ 2 ≠ 0 := by positivity
  have he : (2 : ℝ) ^ (2 * n + 1) < Real.exp ((n : ℝ) ^ 2) := by
    calc
      _ ≤ (2 : ℝ) ^ (n ^ 2) := pow_le_pow_right₀ (by norm_num) hn2
      _ < Real.exp 1 ^ (n ^ 2) := pow_lt_pow_left₀ htwo (by norm_num) hnonzero
      _ = _ := by rw [← Real.exp_nat_mul]; simp
  have hreal : ((2 : ℝ) ^ n * 2) / Real.exp ((n : ℝ) ^ 2) < 1 / (2 : ℝ) ^ n := by
    apply (div_lt_div_iff₀ (Real.exp_pos _) (by positivity)).mpr
    have he' : (2 : ℝ) ^ n * 2 * 2 ^ n < Real.exp ((n : ℝ) ^ 2) := by
      convert he using 1
      rw [pow_add, pow_one, show 2 * n = n + n by omega, pow_add]
      ring
    simpa only [one_mul] using he'
  apply (ENNReal.toReal_lt_toReal
    (ENNReal.mul_ne_top (by finiteness) (tailBound_ne_top n)) (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat, tailBound,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.exp (-((n : ℝ) ^ 2)))]
  rw [Real.exp_neg]
  convert hreal using 1 <;> simp only [div_eq_mul_inv] <;> ring

end AverageCaseComplexity.Completeness.TwoQuery
