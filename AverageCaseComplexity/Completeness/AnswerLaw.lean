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

end AverageCaseComplexity.Completeness.TwoQuery
