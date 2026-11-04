module

public import AverageCaseComplexity.Reductions.Closure
public import AverageCaseComplexity.TimeClasses

/-!
# Query-length cutoffs (distributional part of Corollary 2.2)

The cutoff and domination use the same exceptional set. A cutoff aborts before
calling the target solver; it is not an assumption that the solver is inexpensive
on queries the reduction only makes on exceptional inputs.
-/

@[expose] public section

namespace AverageCaseComplexity

namespace PolyTimeOracleScheme

/-- Domination together with a sharper query-length bound outside the *same*
exceptional set. `cap` can depend on the actual source input. -/
structure CutoffBound (T : PolyTimeOracleScheme) (source target : DistributionalProblem)
    (cap : Word × Accuracy → ℕ) where
  coefficient : ℕ
  degree : ℕ
  domination : ∀ k n, ∃ E : Set (FixedWord n),
    eventProb (source.distribution n) E ≤ k.bound ∧
    (∀ y, T.queryMass target.language source.distribution k n E y ≤
      (dominationFactor coefficient degree n k : ENNReal) * target.distribution.wordMass y) ∧
    ∀ w : FixedWord n, w ∉ E → ∀ y, T.Asks target.language w.toWord k y →
      y.length ≤ cap (w.toWord, k)

/-- Abort on oversized queries *before* invoking the target algorithm. -/
def cutoffAnswer (T : PolyTimeOracleScheme) (A : DeterministicScheme)
    (cap : Word × Accuracy → ℕ) (coefficient degree : ℕ) (a : Word × Accuracy) (y : Word) : Answer :=
  if y.length ≤ cap a then A y (T.simulationAccuracy coefficient degree a) else none

def cutoffSimulatedScheme (T : PolyTimeOracleScheme) (A : DeterministicScheme)
    (cap : Word × Accuracy → ℕ) (coefficient degree : ℕ) : DeterministicScheme :=
  fun x k => T.simulate (T.cutoffAnswer A cap coefficient degree) (x, k.triple)

/-- Cutoff substitution preserves the probability budget. It only differs from
ordinary substitution on queries made inside the exceptional set. -/
theorem cutoffSimulatedScheme_heuristic (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : DeterministicScheme)
    (hT : (T.run target.language).HeuristicConditions source)
    (hA : A.HeuristicConditions target) {cap : Word × Accuracy → ℕ}
    (bound : T.CutoffBound source target cap) :
    (T.cutoffSimulatedScheme A cap bound.coefficient bound.degree).HeuristicConditions source := by
  classical
  intro k n
  let u := k.triple
  let j := T.simulationAccuracy bound.coefficient bound.degree (List.replicate n false, u)
  let bad : Word → Prop := fun y => A y j ≠ some (target.language y)
  obtain ⟨E, hE, hEy, hcap⟩ := bound.domination u n
  let fails : FixedWord n → Prop := fun w =>
    T.run target.language w.toWord u ≠ some (source.language w.toWord)
  let queryBad : FixedWord n → Prop := fun w =>
    w ∉ E ∧ ∃ y, T.Asks target.language w.toWord u y ∧ bad y
  have hcontain : ∀ w : FixedWord n,
      T.cutoffSimulatedScheme A cap bound.coefficient bound.degree w.toWord k ≠
        some (source.language w.toWord) → fails w ∨ (w ∈ E ∨ queryBad w) := by
    intro w hw
    by_cases hf : fails w
    · exact Or.inl hf
    right
    by_cases he : w ∈ E
    · exact Or.inl he
    right
    refine ⟨he, ?_⟩
    by_contra hno
    have hacc := T.simulationAccuracy_eq_length bound.coefficient bound.degree n u
      w.toWord (by simp)
    have heq := T.simulate_eq_of_answers target.language
      (T.cutoffAnswer A cap bound.coefficient bound.degree) (w.toWord, u) (by
        intro y hy
        unfold cutoffAnswer
        rw [ite_eq_left (hcap w he y hy), hacc]
        exact not_ne_iff.mp (fun hb => hno ⟨y, hy, hb⟩))
    change T.simulate _ (w.toWord, u) ≠ _ at hw
    rw [heq] at hw
    exact hw (not_ne_iff.mp hf)
  have hquery : eventProb (source.distribution n) queryBad ≤ u.bound := by
    exact (badQueryEventProb_le T source target u n E
      (dominationFactor bound.coefficient bound.degree n u) j.bound hEy bad
      (fun m _ => (hA j m).le)).trans
      (T.simulationAccuracy_budget bound.coefficient bound.degree n u)
  have hunion : eventProb (source.distribution n) (fun w => w ∈ E ∨ queryBad w) ≤
      u.bound + u.bound :=
    (eventProb_le_add (source.distribution n) (fun _ h => h)).trans (add_le_add hE hquery)
  have hthree : u.bound + (u.bound + u.bound) = k.bound := by
    calc
      _ = 3 * k.triple.bound := by change k.triple.bound + _ = _; ring
      _ = k.bound := by
        rw [Accuracy.triple_bound, div_eq_mul_inv, mul_left_comm]
        simp [ENNReal.mul_inv_cancel (by norm_num : (3 : ENNReal) ≠ 0) (by simp)]
  calc
    source.distribution.prob n
        (fun x => T.cutoffSimulatedScheme A cap bound.coefficient bound.degree x k ≠
          some (source.language x))
      ≤ eventProb (source.distribution n) fails +
          eventProb (source.distribution n) (fun w => w ∈ E ∨ queryBad w) :=
        eventProb_le_add (source.distribution n) hcontain
    _ ≤ eventProb (source.distribution n) fails + (u.bound + u.bound) :=
      add_le_add le_rfl hunion
    _ < u.bound + (u.bound + u.bound) := by
      apply ENNReal.add_lt_add_right
        (by simp [u, Accuracy.bound, Accuracy.triple, Nat.ne_of_gt k.property])
      exact hT u n
    _ = k.bound := hthree

/-- Support-correct target solvers remain safe under the explicit support repair;
an oversized query produces give-up rather than a call outside the cutoff. -/
theorem cutoffSimulatedScheme_correct (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : DeterministicScheme)
    (hT : (T.run target.language).Correct source) (hA : A.Correct target)
    (hsupport : T.QueriesSupported source target) (cap : Word × Accuracy → ℕ)
    (coefficient degree : ℕ) :
    (T.cutoffSimulatedScheme A cap coefficient degree).Correct source := by
  intro k x hx
  have hh := T.simulate_eq_none_or_run target.language
    (T.cutoffAnswer A cap coefficient degree) (x, k.triple) (by
      intro y hy
      unfold cutoffAnswer
      split
      · exact hA _ y (hsupport k.triple x hx y hy)
      · exact Or.inr rfl)
  rcases hh with hh | hh
  · exact Or.inr hh
  · change IsAllowed source.language x (T.simulate _ (x, k.triple))
    rw [hh]
    exact hT k.triple x hx

theorem cutoffSimulatedScheme_correct_of_global (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : DeterministicScheme)
    (hT : (T.run target.language).Correct source)
    (hA : ∀ k y, IsAllowed target.language y (A y k)) (cap : Word × Accuracy → ℕ)
    (coefficient degree : ℕ) :
    (T.cutoffSimulatedScheme A cap coefficient degree).Correct source := by
  intro k x hx
  have hh := T.simulate_eq_none_or_run target.language
    (T.cutoffAnswer A cap coefficient degree) (x, k.triple) (by
      intro y _
      unfold cutoffAnswer
      split
      · exact hA _ y
      · exact Or.inr rfl)
  rcases hh with hh | hh
  · exact Or.inr hh
  · change IsAllowed source.language x (T.simulate _ (x, k.triple))
    rw [hh]
    exact hT k.triple x hx

/-- Semantic errorless transfer, with the support obligation left explicit. -/
theorem cutoffSimulatedScheme_errorless (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : DeterministicScheme)
    (hT : (T.run target.language).ErrorlessConditions source)
    (hA : A.ErrorlessConditions target) (hsupport : T.QueriesSupported source target)
    {cap : Word × Accuracy → ℕ} (bound : T.CutoffBound source target cap) :
    (T.cutoffSimulatedScheme A cap bound.coefficient bound.degree).ErrorlessConditions source := by
  constructor
  · exact T.cutoffSimulatedScheme_correct source target A hT.correct hA.correct hsupport cap
      bound.coefficient bound.degree
  · have hh := T.cutoffSimulatedScheme_heuristic source target A hT.toHeuristic hA.toHeuristic bound
    intro k n
    apply lt_of_le_of_lt (source.distribution.prob_mono_on_support n ?_) (hh k n)
    intro x hx hnone
    rw [hnone]
    simp

/-- Alternative pointwise repair using a globally correct target solver. -/
theorem cutoffSimulatedScheme_errorless_of_global (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : DeterministicScheme)
    (hT : (T.run target.language).ErrorlessConditions source)
    (hA : A.ErrorlessConditions target) (hglobal : ∀ k y, IsAllowed target.language y (A y k))
    {cap : Word × Accuracy → ℕ} (bound : T.CutoffBound source target cap) :
    (T.cutoffSimulatedScheme A cap bound.coefficient bound.degree).ErrorlessConditions source := by
  constructor
  · exact T.cutoffSimulatedScheme_correct_of_global source target A hT.correct hglobal cap
      bound.coefficient bound.degree
  · have hh := T.cutoffSimulatedScheme_heuristic source target A hT.toHeuristic hA.toHeuristic bound
    intro k n
    apply lt_of_le_of_lt (source.distribution.prob_mono_on_support n ?_) (hh k n)
    intro x hx hnone
    rw [hnone]
    simp

end PolyTimeOracleScheme

end AverageCaseComplexity
