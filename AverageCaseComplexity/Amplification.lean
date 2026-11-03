module

public import AverageCaseComplexity.Amplification.Bounds
public import AverageCaseComplexity.Amplification.Runtime

@[expose] public section

/-!
# Fixed-threshold amplification for randomized errorless heuristic schemes

Independent three-run plurality boosting achieves any fixed positive internal
error threshold. The input exceptional-set bound `1/k` is unchanged, and strict
polynomial time is preserved. This is a fixed-threshold version of Itsykson's
Lemma 2.1, not yet its exponentially-small-error, polynomial-repetition version.
-/

namespace AverageCaseComplexity

/-- Errorless semantic conditions with an explicit internal-error threshold.
The outer input exceptional-set bound remains `1/k`. -/
structure AmplifiedErrorlessConditions (error : ENNReal) (A : RandomizedScheme)
    (P : DistributionalProblem) : Prop where
  correct : ∀ k x, P.distribution.Supports x →
    wrongProb P.language x (A x k) < error
  useful : ∀ k n, P.distribution.prob n
    (fun x => error ≤ A x k none) < k.bound

/-- Amplification to any fixed positive error threshold, with a strict-PPT witness.
The chosen depth may depend on the threshold, but not on inputs or accuracy indices.
It uses `3^depth` base calls: a constant overhead only because the threshold is fixed. -/
theorem amplification_constant (A : PolyTimeRandomizedScheme) (P : DistributionalProblem)
    (h : A.run.ErrorlessConditions P) (ε : ℝ) (hε : 0 < ε) :
    ∃ depth : ℕ, AmplifiedErrorlessConditions (ENNReal.ofReal ε) (A.amplify depth).run P := by
  obtain ⟨depth, hdepth⟩ := amplifyPMF_exists_depth ε hε
  refine ⟨depth, ⟨?_, ?_⟩⟩
  · intro k x hx
    rw [wrongProb_eq_mass, run_amplify]
    apply hdepth
    exact le_of_lt (by simpa only [wrongProb_eq_mass] using h.correct k x hx)
  · intro k n
    apply lt_of_le_of_lt (P.distribution.prob_mono_on_support n ?_) (h.useful k n)
    intro x _ hnew
    by_contra hold
    have hsmall := hdepth (A.run x k) none (le_of_lt (lt_of_not_ge hold))
    rw [run_amplify] at hnew
    exact (not_lt_of_ge hnew) hsmall

/-- Any strengthened threshold at most `1/4` implies the original conditions. -/
theorem AmplifiedErrorlessConditions.toErrorlessConditions {error : ENNReal}
    {A : RandomizedScheme} {P : DistributionalProblem}
    (h : AmplifiedErrorlessConditions error A P) (herror : error ≤ (1/4 : ENNReal)) :
    A.ErrorlessConditions P := by
  constructor
  · intro k x hx
    exact (h.correct k x hx).trans_le herror
  · intro k n
    apply lt_of_le_of_lt (P.distribution.prob_mono_on_support n ?_) (h.useful k n)
    intro x _ hx
    exact herror.trans hx

/-- Total failure on a useful supported input is below twice the internal threshold. -/
theorem AmplifiedErrorlessConditions.failure_lt {error : ENNReal}
    {A : RandomizedScheme} {P : DistributionalProblem}
    (h : AmplifiedErrorlessConditions error A P) (k : Accuracy) (x : Word)
    (hx : P.distribution.Supports x) (hgiveup : A x k none < error) :
    failureProb P.language x (A x k) < error + error := by
  rw [failureProb_eq_add]
  exact ENNReal.add_lt_add hgiveup (h.correct k x hx)

/-- Strengthened errorless conditions imply heuristic conditions whenever the
sum of the wrong-answer and give-up thresholds is at most `1/4`. -/
theorem AmplifiedErrorlessConditions.toHeuristicConditions {error : ENNReal}
    {A : RandomizedScheme} {P : DistributionalProblem}
    (h : AmplifiedErrorlessConditions error A P)
    (herror : error + error ≤ (1/4 : ENNReal)) : A.HeuristicConditions P := by
  intro k n
  apply lt_of_le_of_lt (P.distribution.prob_mono_on_support n ?_) (h.useful k n)
  intro x hx hfailure
  by_contra hnot
  have hsmall := (h.failure_lt k x hx (lt_of_not_ge hnot)).trans_le herror
  exact (not_lt_of_ge hfailure) hsmall

/-- The randomized inclusion from §2.4, including a strict polynomial-time witness. -/
theorem AvgBPP.toHeurBPP {P : DistributionalProblem} (h : AvgBPP P) : HeurBPP P := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨depth, hboost⟩ := amplification_constant A P hA (1/8) (by norm_num)
  refine ⟨A.amplify depth, hboost.toHeuristicConditions ?_⟩
  apply (ENNReal.toReal_le_toReal (by norm_num) (by norm_num)).mp
  rw [ENNReal.toReal_add (by norm_num) (by norm_num)]
  norm_num

end AverageCaseComplexity
