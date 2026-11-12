module

public import AverageCaseComplexity.Completeness.AnswerLaw
public import Complexity.Probability.Concentration

@[expose] public section

/-! # Independent answer-count tail bounds

These are distributional lemmas, not efficiency certificates. The executable
filter and majority solver must separately implement the corresponding counts.
-/

namespace AverageCaseComplexity.Completeness.TwoQuery

open Cslib.Probability.PMF

/-- Number of occurrences of an answer in a fixed-size independent sample. -/
def answerCount {N : ℕ} (a : Answer) (outcome : Fin N → Answer) : ℕ :=
  ∑ i, if outcome i = a then 1 else 0

private theorem answerCount_cast {N : ℕ} (a : Answer) (outcome : Fin N → Answer) :
    (answerCount a outcome : ℝ) = ∑ i, if outcome i = a then (1 : ℝ) else 0 := by
  simp [answerCount]

/-- Upper tail for the number of occurrences of a fixed answer. The mean
may be below the advertised threshold by more than the supplied gap. -/
theorem answerCount_upper_tail (p : PMF Answer) (a : Answer) (N : ℕ) (hN : 0 < N)
    (q gap : ℝ) (hgap : 0 < gap) (hmean : (p a).toReal + gap ≤ q) :
    (((Cslib.Probability.PMF.pi (fun _ : Fin N => p)).toOuterMeasure
      {outcome | q * N ≤ (answerCount a outcome : ℝ)}).toReal) ≤
        Real.exp (-2 * N * gap ^ 2) := by
  classical
  let score : Fin N → Answer → ℝ := fun _ b => if b = a then 1 else 0
  have hscore (i : Fin N) (b : Answer) (hb : b ∈ p.support) :
      score i b ∈ Set.Icc 0 1 := by
    simp only [score]
    split <;> norm_num
  have hmean' : (∑ i : Fin N, ∑ b : Answer, (p b).toReal * score i b) =
      (N : ℝ) * (p a).toReal := by
    simp [score, Finset.sum_ite_eq', Finset.sum_const, nsmul_eq_mul, mul_comm]
  have htail := Cslib.Probability.PMF.pi_sum_ge_mean_add
    (fun _ : Fin N => p) score (bound := 1) (ε := (N : ℝ) * gap)
    (by norm_num) hscore (by positivity)
  have hmono :
      (((Cslib.Probability.PMF.pi (fun _ : Fin N => p)).toOuterMeasure
        {outcome | q * N ≤ (answerCount a outcome : ℝ)}).toReal) ≤
      (((Cslib.Probability.PMF.pi (fun _ : Fin N => p)).toOuterMeasure
        {outcome | (∑ i, ∑ b, (p b).toReal * score i b) + (N : ℝ) * gap ≤
          ∑ i, score i (outcome i)}).toReal) := by
    apply ENNReal.toReal_mono (toOuterMeasure_ne_top _ _)
    apply PMF.toOuterMeasure_mono
    intro outcome hout
    change (∑ i, ∑ b, (p b).toReal * score i b) + (N : ℝ) * gap ≤
      ∑ i, score i (outcome i)
    rw [hmean']
    change (N : ℝ) * (p a).toReal + (N : ℝ) * gap ≤
      ∑ i, if outcome i = a then 1 else 0
    rw [← answerCount_cast]
    have hm := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg N)
    have hout' : q * N ≤ (answerCount a outcome : ℝ) := hout.1
    nlinarith
  apply hmono.trans
  convert htail using 1
  simp only [Fintype.card_fin, one_pow, mul_one]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  field_simp

/-- Lower tail for the same count. -/
theorem answerCount_lower_tail (p : PMF Answer) (a : Answer) (N : ℕ) (hN : 0 < N)
    (q gap : ℝ) (hgap : 0 < gap) (hmean : q + gap ≤ (p a).toReal) :
    (((Cslib.Probability.PMF.pi (fun _ : Fin N => p)).toOuterMeasure
      {outcome | (answerCount a outcome : ℝ) ≤ q * N}).toReal) ≤
        Real.exp (-2 * N * gap ^ 2) := by
  classical
  let score : Fin N → Answer → ℝ := fun _ b => if b = a then 1 else 0
  have hscore (i : Fin N) (b : Answer) (hb : b ∈ p.support) :
      score i b ∈ Set.Icc 0 1 := by
    simp only [score]
    split <;> norm_num
  have hmean' : (∑ i : Fin N, ∑ b : Answer, (p b).toReal * score i b) =
      (N : ℝ) * (p a).toReal := by
    simp [score, Finset.sum_ite_eq', Finset.sum_const, nsmul_eq_mul, mul_comm]
  have htail := Cslib.Probability.PMF.pi_sum_le_mean_sub
    (fun _ : Fin N => p) score (bound := 1) (ε := (N : ℝ) * gap)
    (by norm_num) hscore (by positivity)
  have hmono :
      (((Cslib.Probability.PMF.pi (fun _ : Fin N => p)).toOuterMeasure
        {outcome | (answerCount a outcome : ℝ) ≤ q * N}).toReal) ≤
      (((Cslib.Probability.PMF.pi (fun _ : Fin N => p)).toOuterMeasure
        {outcome | ∑ i, score i (outcome i) ≤
          (∑ i, ∑ b, (p b).toReal * score i b) - (N : ℝ) * gap}).toReal) := by
    apply ENNReal.toReal_mono (toOuterMeasure_ne_top _ _)
    apply PMF.toOuterMeasure_mono
    intro outcome hout
    change (∑ i, score i (outcome i)) ≤
      (∑ i, ∑ b, (p b).toReal * score i b) - (N : ℝ) * gap
    rw [hmean']
    change (∑ i, if outcome i = a then (1 : ℝ) else 0) ≤
      (N : ℝ) * (p a).toReal - (N : ℝ) * gap
    rw [← answerCount_cast]
    have hm := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg N)
    have hout' : (answerCount a outcome : ℝ) ≤ q * N := hout.1
    nlinarith
  apply hmono.trans
  convert htail using 1
  simp only [Fintype.card_fin, one_pow, mul_one]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  field_simp

/-- The mathematical law of the 90%-reliability filter on `N` samples.
The inequalities use integer counts, as required by an executable filter. -/
noncomputable def reliabilityLaw (p : PMF Answer) (N : ℕ) : PMF Bool :=
  (Cslib.Probability.PMF.pi (fun _ : Fin N => p)).map fun outcome =>
    decide (9 * N ≤ 10 * answerCount (some false) outcome ∨
      9 * N ≤ 10 * answerCount (some true) outcome)

private theorem outerMeasure_or_le {α : Type*} [Fintype α] (p : PMF α)
    (A B : Set α) :
    p.toOuterMeasure {x | x ∈ A ∨ x ∈ B} ≤ p.toOuterMeasure A + p.toOuterMeasure B := by
  classical
  simp only [PMF.toOuterMeasure_apply_fintype, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp_all

/-- If neither Boolean answer has mass above 85%, accepting a 90%-majority
has probability at most twice the one-sided Hoeffding tail. -/
theorem reliabilityLaw_accept_upper (p : PMF Answer) (n : ℕ) (hn : 0 < n)
    (hbad : peak p ≤ (85 / 100 : ENNReal)) :
    reliabilityLaw p (200 * n ^ 2) true ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) ^ 2))) := by
  classical
  let N := 200 * n ^ 2
  let samples := Cslib.Probability.PMF.pi (fun _ : Fin N => p)
  let A : Set (Fin N → Answer) := {o | (9 / 10 : ℝ) * N ≤ answerCount (some false) o}
  let B : Set (Fin N → Answer) := {o | (9 / 10 : ℝ) * N ≤ answerCount (some true) o}
  have hN : 0 < N := by dsimp [N]; positivity
  have hrare (b : Bool) : (p (some b)).toReal + (1 / 20 : ℝ) ≤ 9 / 10 := by
    have hmass : p (some b) ≤ (85 / 100 : ENNReal) := by
      apply le_trans _ hbad
      cases b <;> simp [peak]
    have hreal := (ENNReal.toReal_le_toReal (p.apply_ne_top _) (by finiteness)).mpr hmass
    norm_num at hreal
    linarith
  have htail (b : Bool) :
      samples.toOuterMeasure {o | (9 / 10 : ℝ) * N ≤ answerCount (some b) o} ≤
        ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 2))) := by
    have h := answerCount_upper_tail p (some b) N hN (9 / 10) (1 / 20)
      (by norm_num) (hrare b)
    have hexponent : -2 * (N : ℝ) * (1 / 20 : ℝ) ^ 2 = -((n : ℝ) ^ 2) := by
      simp only [N, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
    rw [hexponent] at h
    apply (ENNReal.toReal_le_toReal (toOuterMeasure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h
  have hevent : reliabilityLaw p N true = samples.toOuterMeasure {o | o ∈ A ∨ o ∈ B} := by
    rw [reliabilityLaw, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext o
    simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
      Set.mem_ofPred_eq, A, B]
    constructor
    · rintro (h | h)
      · left; have h' : (9 : ℝ) * N ≤ 10 * (answerCount (some false) o : ℝ) := by exact_mod_cast h
        linarith
      · right; have h' : (9 : ℝ) * N ≤ 10 * (answerCount (some true) o : ℝ) := by exact_mod_cast h
        linarith
    · rintro (h | h)
      · left; exact_mod_cast (show (9 : ℝ) * N ≤ 10 * (answerCount (some false) o : ℝ) by linarith)
      · right; exact_mod_cast (show (9 : ℝ) * N ≤ 10 * (answerCount (some true) o : ℝ) by linarith)
  rw [hevent]
  calc
    _ ≤ samples.toOuterMeasure A + samples.toOuterMeasure B := outerMeasure_or_le _ _ _
    _ ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 2))) +
        ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 2))) := add_le_add (htail false) (htail true)
    _ = ENNReal.ofReal (2 * Real.exp (-((n : ℝ) ^ 2))) := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      congr 1
      ring

/-- The upper reliability bound includes the zero-trial case: its allowance
is two, so that case follows simply from probability being at most one. -/
theorem reliabilityLaw_accept_upper_all (p : PMF Answer) (n : ℕ)
    (hbad : peak p ≤ (85 / 100 : ENNReal)) :
    reliabilityLaw p (200 * n ^ 2) true ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) ^ 2))) := by
  by_cases hn : 0 < n
  · exact reliabilityLaw_accept_upper p n hn hbad
  · have hzero : n = 0 := by omega
    subst n
    apply (reliabilityLaw p (200 * 0 ^ 2)).coe_le_one true |>.trans
    norm_num

/-- A Boolean answer of mass at least 95% passes the 90%-filter except
with the stated two-sided allowance (the proof only needs one tail). -/
theorem reliabilityLaw_accept_lower (p : PMF Answer) (n : ℕ) (hn : 0 < n)
    (hgood : (95 / 100 : ENNReal) ≤ peak p) :
    1 - ENNReal.ofReal (2 * Real.exp (-((n : ℝ) ^ 2))) ≤
      reliabilityLaw p (200 * n ^ 2) true := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Bool, (95 / 100 : ENNReal) ≤ p (some b) := by
    rcases le_max_iff.mp hgood with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  let N := 200 * n ^ 2
  let samples := Cslib.Probability.PMF.pi (fun _ : Fin N => p)
  have hN : 0 < N := by dsimp [N]; positivity
  have hmean : (9 / 10 : ℝ) + 1 / 20 ≤ (p (some b)).toReal := by
    have h := (ENNReal.toReal_le_toReal (by finiteness) (p.apply_ne_top _)).mpr hb
    norm_num at h
    linarith
  have htail := answerCount_lower_tail p (some b) N hN (9 / 10) (1 / 20)
    (by norm_num) hmean
  have hexponent : -2 * (N : ℝ) * (1 / 20 : ℝ) ^ 2 = -((n : ℝ) ^ 2) := by
    simp only [N, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [hexponent] at htail
  have hreject : reliabilityLaw p N false ≤
      samples.toOuterMeasure {o | (answerCount (some b) o : ℝ) ≤ (9 / 10 : ℝ) * N} := by
    rw [reliabilityLaw, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    apply PMF.toOuterMeasure_mono
    intro o ho
    have hr : ¬ (9 * N ≤ 10 * answerCount (some false) o ∨
        9 * N ≤ 10 * answerCount (some true) o) := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_false_iff_not] using ho.1
    have hc : 10 * answerCount (some b) o < 9 * N := by
      cases b <;> simp_all only [not_or, not_le]
    have hc' : (10 : ℝ) * (answerCount (some b) o : ℝ) < 9 * N := by exact_mod_cast hc
    change (answerCount (some b) o : ℝ) ≤ (9 / 10 : ℝ) * N
    linarith
  have hfalse : (reliabilityLaw p N false).toReal ≤ Real.exp (-((n : ℝ) ^ 2)) :=
    (ENNReal.toReal_mono (toOuterMeasure_ne_top _ _) hreject).trans htail
  have hsum : (reliabilityLaw p N false).toReal + (reliabilityLaw p N true).toReal = 1 := by
    have h := congrArg ENNReal.toReal (reliabilityLaw p N).tsum_coe
    rw [tsum_fintype, ENNReal.toReal_sum (fun a _ => (reliabilityLaw p N).apply_ne_top a)] at h
    simpa [Fintype.sum_bool, add_comm] using h
  have hreal : 1 - 2 * Real.exp (-((n : ℝ) ^ 2)) ≤ (reliabilityLaw p N true).toReal := by
    linarith [Real.exp_pos (-((n : ℝ) ^ 2))]
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_toReal
    ((reliabilityLaw p N).apply_ne_top true)] at h
  simpa only [ENNReal.ofReal_one] using h

end AverageCaseComplexity.Completeness.TwoQuery
