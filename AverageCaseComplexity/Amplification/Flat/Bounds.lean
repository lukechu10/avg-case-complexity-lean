module

public import AverageCaseComplexity.Amplification.Flat.Basic
public import Complexity.Probability.Concentration

@[expose] public section

namespace AverageCaseComplexity

open Cslib.Probability.PMF

private theorem count_ofFn_eq_sum {n : ℕ} [BEq α] [LawfulBEq α]
    (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = ∑ i, if f i == a then 1 else 0 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.count_append,
      List.count_singleton, Fin.sum_univ_castSucc]
    simpa only [beq_iff_eq, Bool.decide_eq_true, List.ofFn] using
      congrArg (fun x : ℕ => x + if f (Fin.last n) == a then 1 else 0)
        (ih (fun i => f i.castSucc))

/-- The probability that flat plurality returns an answer of probability at most one quarter
falls exponentially with the number of independent repetitions. -/
theorem flatPMF_rare_le (p : PMF Answer) (a : Answer) (N : ℕ) (hN : 0 < N)
    (h : (p a).toReal ≤ (1 / 4 : ℝ)) :
    (flatPMF p N a).toReal ≤ Real.exp (-(N : ℝ) / 72) := by
  classical
  let score : Fin N → Answer → ℝ := fun _ b => if b = a then 1 else 0
  let bad : Set (∀ _ : Fin N, Answer) := {outcome | plurality (List.ofFn outcome) = a}
  let tail : Set (∀ _ : Fin N, Answer) := {outcome |
    (∑ i, ∑ b, (p b).toReal * score i b) + (N : ℝ) / 12 ≤
      ∑ i, score i (outcome i)}
  have hscore (i : Fin N) (b : Answer) (hb : b ∈ p.support) :
      score i b ∈ Set.Icc 0 1 := by
    simp only [score]
    split <;> norm_num
  have hmean : (∑ i : Fin N, ∑ b : Answer, (p b).toReal * score i b) =
      (N : ℝ) * (p a).toReal := by
    simp [score, Finset.sum_ite_eq', Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hbad : bad ⊆ tail := by
    intro outcome hout
    have hcount := length_le_three_count_plurality (List.ofFn outcome)
    have hlen : (List.ofFn outcome).length = N := by simp
    have hcount' : N ≤ 3 * (List.ofFn outcome).count a := by
      rw [hout] at hcount
      simpa [hlen] using hcount
    have hsum : ((List.ofFn outcome).count a : ℝ) =
        ∑ i : Fin N, score i (outcome i) := by
      have hc := count_ofFn_eq_sum outcome a
      have hreal : ((List.ofFn outcome).count a : ℝ) =
          ∑ i : Fin N, (if outcome i == a then (1 : ℝ) else 0) := by exact_mod_cast hc
      simpa [score, beq_iff_eq] using hreal
    have hreal : (N : ℝ) / 3 ≤ (∑ i : Fin N, score i (outcome i)) := by
      rw [← hsum]
      have hc : (N : ℝ) ≤ 3 * ((List.ofFn outcome).count a : ℝ) := by exact_mod_cast hcount'
      nlinarith
    have htarget :
        (∑ i : Fin N, ∑ b : Answer, (p b).toReal * score i b) + (N : ℝ) / 12 ≤
          ∑ i, score i (outcome i) := by
      rw [hmean]
      rw [← hsum]
      have hc : (N : ℝ) ≤ 3 * ((List.ofFn outcome).count a : ℝ) := by exact_mod_cast hcount'
      nlinarith [h, mul_nonneg (Nat.cast_nonneg N) (show (p a).toReal ≥ 0 by positivity)]
    exact htarget
  have htail := Cslib.Probability.PMF.pi_sum_ge_mean_add
    (fun _ : Fin N => p) score (bound := 1) (ε := (N : ℝ) / 12) (by norm_num)
    (fun i b hb => hscore i b hb) (by positivity)
  have hprob : ((Cslib.Probability.PMF.pi (fun _ : Fin N => p)).toOuterMeasure bad).toReal ≤
      Real.exp (-(N : ℝ) / 72) := by
    calc
      _ ≤ ((Cslib.Probability.PMF.pi (fun _ : Fin N => p)).toOuterMeasure tail).toReal := by
        apply ENNReal.toReal_mono (toOuterMeasure_ne_top _ _)
        apply (Cslib.Probability.PMF.pi (fun _ : Fin N => p)).toOuterMeasure_mono
        intro outcome hout
        exact hbad hout.1
      _ ≤ Real.exp (-(N : ℝ) / 72) := by
        have hcard : (Fintype.card (Fin N) : ℝ) = (N : ℝ) := by simp
        have hexp : -2 * ((N : ℝ) / 12) ^ 2 /
            ((Fintype.card (Fin N) : ℝ) * 1 ^ 2) = -(N : ℝ) / 72 := by
          rw [hcard]
          have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
          field_simp
          ring
        rw [← hexp]
        exact (by simpa [tail] using htail)
  change (((Cslib.Probability.PMF.pi (fun _ : Fin N => p)).map
      (fun outcome => plurality (List.ofFn outcome))) a).toReal ≤ _
  rw [← PMF.toOuterMeasure_apply_singleton]
  rw [PMF.toOuterMeasure_map_apply]
  have hevent : (fun outcome : ∀ _ : Fin N, Answer => plurality (List.ofFn outcome)) ⁻¹'
      ({a} : Set Answer) = bad := by
    ext outcome
    simp [bad]
  rw [hevent]
  exact hprob

end AverageCaseComplexity
