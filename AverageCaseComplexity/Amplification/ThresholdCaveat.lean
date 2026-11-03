module

public import AverageCaseComplexity.Amplification

@[expose] public section

/-!
# Caveat about the upper threshold in the printed Lemma 2.1

At common internal threshold `2/5`, the fixed law
`P(0)=P(1)=3/8`, `P(give up)=1/4` satisfies the displayed probability conditions
for every language. This warns against interpreting the printed upper interval
as an unrestricted equivalence of complexity classes. It does not contradict
one-way amplification from an existing quarter-error scheme.
Informally this law is realizable using three fair bits. The lemma here checks
the probability conditions only, not a runtime certificate or class separation.
-/

namespace AverageCaseComplexity

/-- Real-valued masses of the fixed three-answer counterexample. -/
noncomputable def looseMass : Answer → ℝ
  | none => 1/4
  | some _ => 3/8

/-- A fixed dyadic output law, independent of both input and language. -/
noncomputable def looseThresholdPMF : PMF Answer :=
  PMF.ofFintype (fun a => ENNReal.ofReal (looseMass a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by cases a <;> norm_num [looseMass])]
    norm_num [Fintype.sum_option, looseMass])

/-- The relaxed `2/5` probability conditions become vacuous for arbitrary languages. -/
theorem looseThreshold_conditions (P : DistributionalProblem) :
    AmplifiedErrorlessConditions (ENNReal.ofReal (2/5)) (fun _ _ => looseThresholdPMF) P := by
  constructor
  · intro k x hx
    rw [wrongProb_eq_mass]
    norm_num [looseThresholdPMF, looseMass]
  · intro k n
    have hnone : ¬ ENNReal.ofReal (2/5) ≤ looseThresholdPMF none := by
      norm_num [looseThresholdPMF, looseMass]
    simp [Ensemble.prob, hnone]

end AverageCaseComplexity
