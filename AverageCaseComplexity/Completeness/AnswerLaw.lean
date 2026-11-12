module

public import AverageCaseComplexity.Amplification

@[expose] public section

/-! # Probability facts for the two-query construction

These facts concern actual three-answer laws, independently of the universal
machine and tuple encoding used to represent instances of the complete problem.
-/

namespace AverageCaseComplexity.Completeness.TwoQuery

/-- Ties between Boolean answers are resolved in favor of false. -/
noncomputable def frequentBit (p : PMF Answer) : Bool :=
  decide (p (some false) < p (some true))

noncomputable def peak (p : PMF Answer) : ENNReal :=
  max (p (some false)) (p (some true))

/-- Agreement returns the common bit; disagreement gives up. -/
def combine (b₀ b₁ : Bool) : Answer := if b₀ = b₁ then some b₀ else none

@[simp] theorem combine_self (b : Bool) : combine b b = some b := by
  simp [combine]

@[simp] theorem combine_eq_none_iff (b₀ b₁ : Bool) :
    combine b₀ b₁ = none ↔ b₀ ≠ b₁ := by
  simp [combine]

/-- A small wrong-answer and give-up mass leave the correct bit as the
strictly more frequent Boolean answer. -/
theorem frequentBit_eq_of_small_wrong_and_giveUp (p : PMF Answer) (b : Bool)
    (hwrong : p (some (!b)) < (1 / 100 : ENNReal))
    (hgiveUp : p none < (1 / 4 : ENNReal)) : frequentBit p = b := by
  have hw := (ENNReal.toReal_lt_toReal (p.apply_ne_top _) (by norm_num)).mpr hwrong
  have hg := (ENNReal.toReal_lt_toReal (p.apply_ne_top _) (by norm_num)).mpr hgiveUp
  norm_num at hw hg
  have hs := answer_mass_sum p
  cases b
  · simp only [Bool.not_false] at hw
    have hlt : p (some true) < p (some false) :=
      (ENNReal.toReal_lt_toReal (p.apply_ne_top _) (p.apply_ne_top _)).mp (by linarith)
    simp [frequentBit, not_lt_of_ge (le_of_lt hlt)]
  · simp only [Bool.not_true] at hw
    have hlt : p (some false) < p (some true) :=
      (ENNReal.toReal_lt_toReal (p.apply_ne_top _) (p.apply_ne_top _)).mp (by linarith)
    simp [frequentBit, hlt]

/-- Outside the source exceptional set, at least 98% of the mass is on one
Boolean answer. Strictness follows from the two strict one-percent bounds. -/
theorem peak_gt_of_small_wrong_and_giveUp (p : PMF Answer) (b : Bool)
    (hwrong : p (some (!b)) < (1 / 100 : ENNReal))
    (hgiveUp : p none < (1 / 100 : ENNReal)) :
    (98 / 100 : ENNReal) < peak p := by
  have hw := (ENNReal.toReal_lt_toReal (p.apply_ne_top _) (by norm_num)).mpr hwrong
  have hg := (ENNReal.toReal_lt_toReal (p.apply_ne_top _) (by norm_num)).mpr hgiveUp
  norm_num at hw hg
  have hs := answer_mass_sum p
  have hb : (98 / 100 : ENNReal) < p (some b) := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (p.apply_ne_top _)).mp
    cases b <;> norm_num at hw ⊢ <;> linarith
  exact hb.trans_le (by cases b <;> simp [peak])

/-- The complete-language bit uses the fallback exactly when the simulated
computation gives up with probability at least one quarter. -/
noncomputable def fallbackBit (p : PMF Answer) (fallback : Bool) : Bool :=
  if (1 / 4 : ENNReal) ≤ p none then fallback else frequentBit p

/-- The less frequent Boolean answer has probability at most one half,
including the tie-breaking case. -/
theorem frequentBit_wrong_le_half (p : PMF Answer) :
    p (some (!frequentBit p)) ≤ (1 / 2 : ENNReal) := by
  have hs := answer_mass_sum p
  have hn := ENNReal.toReal_nonneg (a := p none)
  by_cases h : p (some false) < p (some true)
  · have hr := (ENNReal.toReal_lt_toReal (p.apply_ne_top _) (p.apply_ne_top _)).mpr h
    simp only [frequentBit, h, decide_true, Bool.not_true]
    apply (ENNReal.toReal_le_toReal (p.apply_ne_top _) (by finiteness)).mp
    norm_num
    linarith
  · have hr := (ENNReal.toReal_le_toReal (p.apply_ne_top _) (p.apply_ne_top _)).mpr
      (le_of_not_gt h)
    simp only [frequentBit, h, decide_false, Bool.not_false]
    apply (ENNReal.toReal_le_toReal (p.apply_ne_top _) (by finiteness)).mp
    norm_num
    linarith

/-- For either fallback choice, the Boolean answer opposite the complete
language has mass at most three quarters. This is the gap used by its 80%-vote
solver, independently of how the simulated machine was encoded. -/
theorem fallbackBit_wrong_le_threeQuarters (p : PMF Answer) (fallback : Bool) :
    p (some (!fallbackBit p fallback)) ≤ (3 / 4 : ENNReal) := by
  by_cases hg : (1 / 4 : ENNReal) ≤ p none
  · simp only [fallbackBit, ite_eq_left hg]
    have hr := (ENNReal.toReal_le_toReal (by finiteness) (p.apply_ne_top _)).mpr hg
    norm_num at hr
    have hs := answer_mass_sum p
    apply (ENNReal.toReal_le_toReal (p.apply_ne_top _) (by finiteness)).mp
    cases fallback <;> norm_num <;>
      linarith [ENNReal.toReal_nonneg (a := p (some false)),
        ENNReal.toReal_nonneg (a := p (some true))]
  · simp only [fallbackBit, ite_eq_right hg]
    exact (frequentBit_wrong_le_half p).trans (by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num)

end AverageCaseComplexity.Completeness.TwoQuery
