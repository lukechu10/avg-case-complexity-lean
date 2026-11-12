module

public import AverageCaseComplexity.Completeness.ThresholdBounds
public import AverageCaseComplexity.Completeness.TailBounds

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Cslib.Probability.PMF

/-- Return an 80%-majority Boolean answer if one exists, otherwise give up.
The integer comparisons avoid real arithmetic in the executable decision. -/
def majorityAnswer {N : ℕ} (outcome : Fin N → Answer) : Answer :=
  if 4 * N ≤ 5 * answerCount (some false) outcome then some false
  else if 4 * N ≤ 5 * answerCount (some true) outcome then some true
  else none

theorem majorityAnswer_count {N : ℕ} (outcome : Fin N → Answer) (b : Bool)
    (h : majorityAnswer outcome = some b) :
    4 * N ≤ 5 * answerCount (some b) outcome := by
  unfold majorityAnswer at h
  split_ifs at h with hf ht
  · cases b <;> simp_all
  · cases b <;> simp_all

@[simp] theorem majorityAnswer_eq_none_iff {N : ℕ} (outcome : Fin N → Answer) :
    majorityAnswer outcome = none ↔
      ¬ 4 * N ≤ 5 * answerCount (some false) outcome ∧
      ¬ 4 * N ≤ 5 * answerCount (some true) outcome := by
  by_cases hf : 4 * N ≤ 5 * answerCount (some false) outcome <;>
    by_cases ht : 4 * N ≤ 5 * answerCount (some true) outcome <;>
    simp [majorityAnswer, hf, ht]

/-- Distributional semantics of the finite-sample majority branch. -/
noncomputable def majorityLaw (p : PMF Answer) (N : ℕ) : PMF Answer :=
  (Cslib.Probability.PMF.pi (fun _ : Fin N => p)).map majorityAnswer

/-- An answer of probability at most 75% is exponentially unlikely to
occupy 80% of an independent sample. -/
theorem majorityLaw_rare (p : PMF Answer) (b : Bool) (N : ℕ) (hN : 0 < N)
    (hrare : p (some b) ≤ (3 / 4 : ENNReal)) :
    majorityLaw p N (some b) ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 200)) := by
  classical
  let samples := Cslib.Probability.PMF.pi (fun _ : Fin N => p)
  have hmean : (p (some b)).toReal + (1 / 20 : ℝ) ≤ 4 / 5 := by
    have h := (ENNReal.toReal_le_toReal (p.apply_ne_top _) (by finiteness)).mpr hrare
    norm_num at h
    linarith
  have htail := answerCount_upper_tail p (some b) N hN (4 / 5) (1 / 20)
    (by norm_num) hmean
  have hexponent : -2 * (N : ℝ) * (1 / 20 : ℝ) ^ 2 = -(N : ℝ) / 200 := by ring
  rw [hexponent] at htail
  have hbound : majorityLaw p N (some b) ≤
      samples.toOuterMeasure {o | (4 / 5 : ℝ) * N ≤ answerCount (some b) o} := by
    rw [majorityLaw, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    apply PMF.toOuterMeasure_mono
    intro o ho
    have hc := majorityAnswer_count o b ho.1
    have hc' : (4 : ℝ) * N ≤ 5 * (answerCount (some b) o : ℝ) := by exact_mod_cast hc
    change (4 / 5 : ℝ) * N ≤ answerCount (some b) o
    linarith
  apply (ENNReal.toReal_le_toReal ((majorityLaw p N).apply_ne_top _)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  exact (ENNReal.toReal_mono (toOuterMeasure_ne_top _ _) hbound).trans htail

/-- A small elementary exponential bound suffices for the correctness constant.
The actual construction uses a much larger burn-in. -/
theorem single_tail_lt_quarter {m : ℕ} (hm : 2 ≤ m) :
    ENNReal.ofReal (Real.exp (-((m : ℝ) ^ 2))) < (1 / 4 : ENNReal) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have he := Real.add_one_le_exp ((m : ℝ) ^ 2)
  have hexp : (4 : ℝ) < Real.exp ((m : ℝ) ^ 2) := by nlinarith
  apply (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (by finiteness)).mp
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), Real.exp_neg]
  norm_num
  simpa only [one_div] using inv_strictAnti₀ (by norm_num) hexp

/-- Probability-level pointwise correctness of the non-exact solver branch
for the complete-language truth table, for either fallback value. -/
theorem majorityLaw_wrong_lt_quarter (p : PMF Answer) (fallback : Bool)
    (m : ℕ) (hm : 2 ≤ m) :
    majorityLaw p (200 * m ^ 2) (some (!fallbackBit p fallback)) < (1 / 4 : ENNReal) := by
  have hN : 0 < 200 * m ^ 2 := by positivity
  have h := majorityLaw_rare p (!fallbackBit p fallback) (200 * m ^ 2) hN
    (fallbackBit_wrong_le_threeQuarters p fallback)
  have hexponent : -((200 * m ^ 2 : ℕ) : ℝ) / 200 = -((m : ℝ) ^ 2) := by
    push_cast
    ring
  rw [hexponent] at h
  exact h.trans_lt (single_tail_lt_quarter hm)

/-- A law with a Boolean answer of mass at least 85% rarely gives up
under the 80%-majority solver. -/
theorem majorityLaw_giveUp (p : PMF Answer) (N : ℕ) (hN : 0 < N)
    (hgood : (85 / 100 : ENNReal) ≤ peak p) :
    majorityLaw p N none ≤ ENNReal.ofReal (Real.exp (-(N : ℝ) / 200)) := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Bool, (85 / 100 : ENNReal) ≤ p (some b) := by
    rcases le_max_iff.mp hgood with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  let samples := Cslib.Probability.PMF.pi (fun _ : Fin N => p)
  have hmean : (4 / 5 : ℝ) + 1 / 20 ≤ (p (some b)).toReal := by
    have h := (ENNReal.toReal_le_toReal (by finiteness) (p.apply_ne_top _)).mpr hb
    norm_num at h
    linarith
  have htail := answerCount_lower_tail p (some b) N hN (4 / 5) (1 / 20)
    (by norm_num) hmean
  have hexponent : -2 * (N : ℝ) * (1 / 20 : ℝ) ^ 2 = -(N : ℝ) / 200 := by ring
  rw [hexponent] at htail
  have hbound : majorityLaw p N none ≤
      samples.toOuterMeasure {o | (answerCount (some b) o : ℝ) ≤ (4 / 5 : ℝ) * N} := by
    rw [majorityLaw, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    apply PMF.toOuterMeasure_mono
    intro o ho
    have hnone := (majorityAnswer_eq_none_iff o).mp ho.1
    have hc : 5 * answerCount (some b) o < 4 * N := by
      cases b <;> omega
    have hc' : (5 : ℝ) * (answerCount (some b) o : ℝ) < 4 * N := by exact_mod_cast hc
    change (answerCount (some b) o : ℝ) ≤ (4 / 5 : ℝ) * N
    linarith
  apply (ENNReal.toReal_le_toReal ((majorityLaw p N).apply_ne_top _)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  exact (ENNReal.toReal_mono (toOuterMeasure_ne_top _ _) hbound).trans htail

end AverageCaseComplexity.Completeness.TwoQuery
