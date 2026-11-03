import AverageCaseComplexity

open AverageCaseComplexity

-- Flat plurality handles both repeated answers and all-distinct ties explicitly.
example : plurality [some true, none, some true] = some true := by decide
example : plurality [none, some false, some true] = none := by decide
example : plurality [some false, some true] = some false := by decide

-- Zero runs are defined, but the concentration theorem requires a positive count.
example (program : Cslib.ProbComp Answer) : flatProgram program 0 = pure none := by
  simp [flatProgram, plurality]

-- The repetition count remains positive even for empty input and k = 1.
example : linearRepeatCount 2 ([], ⟨1, by decide⟩) = 648 := rfl

-- Hoeffding supplies an explicit exponential bound at every positive repetition count.
example (p : PMF Answer) (a : Answer) (N : ℕ) (hN : 0 < N)
    (h : (p a).toReal ≤ (1/4 : ℝ)) :
    (flatPMF p N a).toReal ≤ Real.exp (-(N : ℝ) / 72) := flatPMF_rare_le p a N hN h

-- The main theorem includes the runtime certificate and preserves the outer bound 1/k.
example (A : PolyTimeRandomizedScheme) (P : DistributionalProblem)
    (h : A.run.ErrorlessConditions P) (rate : ℕ) :
    LengthErrorlessConditions (exponentialError rate) (A.flatAmplifyLinear rate).run P :=
  amplification_exponential A P h rate

-- Rate two is small enough at every length to retain the original AvgBPP guarantees.
example (A : PolyTimeRandomizedScheme) (P : DistributionalProblem)
    (h : A.run.ErrorlessConditions P) : (A.flatAmplifyLinear 2).run.ErrorlessConditions P :=
  (amplification_exponential A P h 2).toErrorlessConditions
    (fun n => (exponentialError_lt_quarter 2 n (by decide)).le)

example (P : DistributionalProblem) : AvgBPP P ↔
    ∃ B : PolyTimeRandomizedScheme, LengthErrorlessConditions (exponentialError 2) B.run P :=
  avgBPP_iff_exponential P 2 (by decide)

-- Any looser length-dependent target can be substituted without computing that target.
example (A : PolyTimeRandomizedScheme) (P : DistributionalProblem)
    (h : A.run.ErrorlessConditions P) (error : ℕ → ENNReal)
    (hlower : ∀ n, exponentialError 2 n ≤ error n) :
    ∃ B : PolyTimeRandomizedScheme, LengthErrorlessConditions error B.run P :=
  amplification_for_thresholds A P h error 2 hlower

-- The paper's unrestricted upper-threshold claim is not assumed:
-- at 2/5 a fixed dyadic law meets the displayed probability conditions for any language.
example (P : DistributionalProblem) :
    AmplifiedErrorlessConditions (ENNReal.ofReal (2/5)) (fun _ _ => looseThresholdPMF) P :=
  looseThreshold_conditions P
