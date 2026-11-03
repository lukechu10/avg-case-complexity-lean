import AverageCaseComplexity

open AverageCaseComplexity

-- Every position of the repeated answer wins; all-distinct ties choose the first.
example : plurality3 none (some true) (some true) = some true := by decide
example : plurality3 (some false) none (some false) = some false := by decide
example : plurality3 (some true) (some true) none = some true := by decide
example : plurality3 none (some false) (some true) = none := by decide
example : plurality3 (some false) none (some true) = some false := by decide

-- Amplification never changes an exact constant answer, even a constant give-up.
example (a : Answer) : amplifyPMF (PMF.pure a) 8 = PMF.pure a := by simp

-- The contraction includes the boundary p = 1/4, not just strictly smaller masses.
example (p : PMF Answer) (a : Answer) (h : p a ≤ (1/4 : ENNReal)) :
    amplifyPMF p 8 a < (1/8 : ENNReal) := amplifyPMF_eight_lt_ennreal p a h

-- Any fixed positive target can be used, e.g. one percent.
example (A : PolyTimeRandomizedScheme) (P : DistributionalProblem)
    (h : A.run.ErrorlessConditions P) :
    ∃ depth, AmplifiedErrorlessConditions (ENNReal.ofReal (1/100)) (A.amplify depth).run P :=
  amplification_constant A P h _ (by norm_num)

-- Strengthening preserves the original guarantees at any sufficiently small threshold.
example (A : RandomizedScheme) (P : DistributionalProblem) (error : ENNReal)
    (h : AmplifiedErrorlessConditions error A P) (he : error ≤ (1/4 : ENNReal)) :
    A.ErrorlessConditions P := h.toErrorlessConditions he

-- The conversion to heuristic guarantees is also independent of a particular threshold.
example (A : RandomizedScheme) (P : DistributionalProblem) (error : ENNReal)
    (h : AmplifiedErrorlessConditions error A P) (he : error + error ≤ (1/4 : ENNReal)) :
    A.HeuristicConditions P := h.toHeuristicConditions he

-- The class inclusion retains a machine certificate, also under PSamp.
example (P : DistributionalProblem) (h : AvgBPP P) : HeurBPP P := h.toHeurBPP

example (P : DistributionalProblem) (h : WithPSamp AvgBPP P) : WithPSamp HeurBPP P :=
  WithPSamp.mono (fun _ hP => hP.toHeurBPP) h
