module

public import AverageCaseComplexity.Amplification.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace AverageCaseComplexity

/-- Finite bind, expressed in real-valued probabilities. -/
theorem pmf_bind_toReal {α β : Type*} [Fintype α]
    (p : PMF α) (f : α → PMF β) (b : β) :
    (p.bind f b).toReal = ∑ a, (p a).toReal * (f a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (p.apply_ne_top a) ((f a).apply_ne_top b)

/-- The three answer probabilities sum to one. -/
theorem answer_mass_sum (p : PMF Answer) :
    (p none).toReal + (p (some false)).toReal + (p (some true)).toReal = 1 := by
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  have hreal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)] at hreal
  simpa [Fintype.sum_option, Fintype.sum_bool, add_comm, add_left_comm, add_assoc] using hreal

/-- Exact finite formula for the marginal of the symmetric plurality vote. -/
theorem boostPMF_mass (p : PMF Answer) (a : Answer) :
    (boostPMF p a).toReal = (p a).toReal ^ 2 + 2 * (p a).toReal *
      ((p none).toReal * (p (some false)).toReal +
       (p none).toReal * (p (some true)).toReal +
       (p (some false)).toReal * (p (some true)).toReal) := by
  have raw : (boostPMF p a).toReal = (p a).toReal ^ 2 *
      ((p none).toReal + (p (some false)).toReal + (p (some true)).toReal) +
      2 * (p a).toReal *
      ((p none).toReal * (p (some false)).toReal +
       (p none).toReal * (p (some true)).toReal +
       (p (some false)).toReal * (p (some true)).toReal) := by
    unfold boostPMF
    simp_rw [pmf_bind_toReal]
    cases a with
    | none =>
      simp [Fintype.sum_option, plurality3, PMF.pure_apply]
      ring
    | some b =>
      cases b <;>
        simp [Fintype.sum_option, plurality3, PMF.pure_apply] <;> ring
  rw [raw, answer_mass_sum, mul_one]

/-- Numerical contraction for any one of three categories of mass at most `1/4`. -/
private theorem plurality_contraction (u v w : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1/4)
    (hsum : u + v + w = 1) :
    u ^ 2 + 2 * u * (u*v + u*w + v*w) ≤ (29/32 : ℝ) * u := by
  have hcomp : v + w = 1 - u := by linarith
  have hcross : 4*v*w ≤ (1-u)^2 := by
    calc
      4*v*w ≤ (v+w)^2 := by nlinarith [sq_nonneg (v-w)]
      _ = (1-u)^2 := by rw [hcomp]
  have hgap : 0 ≤ (1/4-u) * (13/8-3/2*u) :=
    mul_nonneg (by linarith) (by linarith)
  have hratio : u + 2 * (u*v + u*w + v*w) ≤ (29/32 : ℝ) := by
    have heq : u + 2 * (u*v + u*w + v*w) = u + 2*u*(1-u) + 2*v*w := by
      rw [← hcomp]
      ring
    rw [heq]
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hratio hu
  nlinarith only [hmul]

/-- Each rare answer contracts by a fixed factor, regardless of the other two masses. -/
theorem boostPMF_contract (p : PMF Answer) (a : Answer)
    (h : (p a).toReal ≤ (1/4 : ℝ)) :
    (boostPMF p a).toReal ≤ (29/32 : ℝ) * (p a).toReal := by
  rw [boostPMF_mass]
  have hs := answer_mass_sum p
  cases a with
  | none =>
    exact plurality_contraction _ _ _ ENNReal.toReal_nonneg h hs
  | some b =>
    cases b
    · have hc := plurality_contraction (p (some false)).toReal (p none).toReal
        (p (some true)).toReal ENNReal.toReal_nonneg h (by linarith)
      nlinarith only [hc]
    · have hc := plurality_contraction (p (some true)).toReal (p none).toReal
        (p (some false)).toReal ENNReal.toReal_nonneg h (by linarith)
      nlinarith only [hc]

/-- Iterated fixed-factor amplification of any initially rare answer. -/
theorem amplifyPMF_contract (p : PMF Answer) (a : Answer) (depth : ℕ)
    (h : (p a).toReal ≤ (1/4 : ℝ)) :
    (amplifyPMF p depth a).toReal ≤ (29/32 : ℝ)^depth * (p a).toReal := by
  induction depth with
  | zero => simp [amplifyPMF]
  | succ depth ih =>
    have hpow : (29/32 : ℝ)^depth ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hrare : (amplifyPMF p depth a).toReal ≤ (1/4 : ℝ) :=
      ih.trans ((mul_le_of_le_one_left ENNReal.toReal_nonneg hpow).trans h)
    calc
      (amplifyPMF p (depth+1) a).toReal ≤
          (29/32 : ℝ) * (amplifyPMF p depth a).toReal := boostPMF_contract _ _ hrare
      _ ≤ (29/32 : ℝ) * ((29/32 : ℝ)^depth * (p a).toReal) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (29/32 : ℝ)^(depth+1) * (p a).toReal := by rw [pow_succ]; ring

/-- Eight fixed boosting levels reduce each rare answer below `1/8`.
There are `3^8 = 6561` independent base calls, a constant runtime factor. -/
theorem amplifyPMF_eight_lt (p : PMF Answer) (a : Answer)
    (h : (p a).toReal ≤ (1/4 : ℝ)) :
    (amplifyPMF p 8 a).toReal < (1/8 : ℝ) := by
  have hc := amplifyPMF_contract p a 8 h
  have hmul := mul_le_mul_of_nonneg_left h (by norm_num : 0 ≤ (29/32 : ℝ)^8)
  norm_num at hmul
  linarith

/-- The fixed-depth bound in the probability type used by scheme definitions. -/
theorem amplifyPMF_eight_lt_ennreal (p : PMF Answer) (a : Answer)
    (h : p a ≤ (1/4 : ENNReal)) : amplifyPMF p 8 a < (1/8 : ENNReal) := by
  have hr := (ENNReal.toReal_le_toReal (p.apply_ne_top a) (by norm_num)).mpr h
  norm_num at hr
  apply (ENNReal.toReal_lt_toReal ((amplifyPMF p 8).apply_ne_top a) (by norm_num)).mp
  norm_num
  exact amplifyPMF_eight_lt p a hr

/-- Any fixed positive target error is achieved by some fixed boosting depth.
The depth is uniform over all input distributions and all three answer values. -/
theorem amplifyPMF_exists_depth (ε : ℝ) (hε : 0 < ε) :
    ∃ depth : ℕ, ∀ (p : PMF Answer) (a : Answer), p a ≤ (1/4 : ENNReal) →
      amplifyPMF p depth a < ENNReal.ofReal ε := by
  obtain ⟨depth, hdepth⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (29/32 : ℝ) < 1)
  refine ⟨depth, fun p a h => ?_⟩
  have hr := (ENNReal.toReal_le_toReal (p.apply_ne_top a) (by norm_num)).mpr h
  norm_num at hr
  have hc := amplifyPMF_contract p a depth hr
  have hunit : (p a).toReal ≤ 1 := hr.trans (by norm_num)
  have hmul : (29/32 : ℝ)^depth * (p a).toReal ≤ (29/32 : ℝ)^depth :=
    mul_le_of_le_one_right (by positivity) hunit
  apply (ENNReal.toReal_lt_toReal ((amplifyPMF p depth).apply_ne_top a)
    ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hε.le]
  exact (hc.trans hmul).trans_lt hdepth

end AverageCaseComplexity
