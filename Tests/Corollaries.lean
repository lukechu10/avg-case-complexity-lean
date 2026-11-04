import AverageCaseComplexity

open AverageCaseComplexity Turing.MultiTapeTM

-- Corollary 2.1(2), for arbitrary length-dependent target budgets.
example {T : PolyTimeOracleScheme} {source target : DistributionalProblem}
    (hT : HeuristicReductionConditions T source target) {η : ℕ → ENNReal}
    (bound : T.FixedBudgetBound source target η) (htarget : HeurFixedP η target) : HeurP source :=
  hT.toHeurP_of_fixedBudget bound htarget

-- Corollary 2.1(1) requires no query-support hypothesis: fixed-budget errorlessness
-- is global, unlike adjustable-accuracy AvgP correctness.
example {T : PolyTimeOracleScheme} {source target : DistributionalProblem}
    (hT : ErrorlessReductionConditions T source target) {η : ℕ → ENNReal}
    (bound : T.FixedBudgetBound source target η) (htarget : AvgFixedP η target) : AvgP source :=
  hT.toAvgP_of_fixedBudget bound htarget

-- Inverse-polynomial specialization uses the same domination witness as its budget.
example {T : PolyTimeOracleScheme} {source target : DistributionalProblem}
    (hT : ErrorlessReductionConditions T source target) (c coefficient degree : ℕ)
    (lengthCount : ℕ → Accuracy → ℕ)
    (hcover : ∀ k n, ∃ lengths : Finset ℕ, lengths.card ≤ lengthCount n k ∧
      ∀ w : FixedWord n, ∀ y, T.Asks target.language w.toWord k y → y.length ∈ lengths)
    (hdom : ∀ k n, ∃ E : Set (FixedWord n),
      eventProb (source.distribution n) E ≤ k.bound ∧
      ∀ y, T.queryMass target.language source.distribution k n E y ≤
        (PolyTimeOracleScheme.dominationFactor coefficient degree n k : ENNReal) *
          target.distribution.wordMass y)
    (hlength : ∀ k x y, T.Asks target.language x k y →
      (PolyTimeOracleScheme.fixedBudgetAccuracy coefficient degree x.length k
        (lengthCount x.length k)).val ≤ y.length ^ c)
    (htarget : AvgFixedP (inversePolynomialError c) target) : AvgP source :=
  hT.toAvgP_of_fixedBudget
    (PolyTimeOracleScheme.FixedBudgetBound.of_inversePolynomial T source target c coefficient degree
      lengthCount hcover hdom hlength) htarget

-- Padding remains meaningful for exponent one: the budget uses one distinct
-- query length, not the potentially much larger maximum query length.
example : (PolyTimeOracleScheme.fixedBudgetAccuracy 0 0 10 ⟨1, by decide⟩ 1).val = 26 := rfl
example : (PolyTimeOracleScheme.fixedBudgetAccuracy 0 0 10 ⟨1, by decide⟩ 1).val ≤
    (List.replicate 26 false).length ^ 1 := by decide

-- A real machine-certified, never-giving-up fixed target algorithm.
def fixedFalse : PolyTimeDeterministicAlgorithm where
  run := fun _ => some false
  efficient := .const (some false)

example (D : Ensemble) : AvgFixedP (inversePolynomialError 2) ⟨fun _ => false, D⟩ := by
  refine ⟨fixedFalse, ⟨fun _ => Or.inl rfl, ?_⟩⟩
  intro n
  simp [fixedFalse, Ensemble.prob, eventProb, inversePolynomialError]

-- Real exponents, not just natural powers, are available for Corollary 2.1.
example {c : ℝ} {n : ℕ} {j : Accuracy}
    (h : (j.val : ENNReal) ≤ (n : ENNReal) ^ c) : inversePowerError c n ≤ j.bound :=
  inversePowerError_le_bound h

-- Positive accuracy rules out an empty query under a positive power lower bound.
example (j : Accuracy) (c : ℕ) : ¬ j.val ≤ (0 : ℕ) ^ (c + 1) := by
  simpa using Nat.not_le_of_gt j.property

-- Arbitrary-bound classes have actual time-and-space machine witnesses.
def linearFalse : TimeBoundedDeterministicScheme
    (fun a => (schemeInputEncoding a).length + 1) where
  run := fun _ _ => some false
  efficient := (ComputableTidilyInO.const (some false)).mono_le
    (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _)

example (D : Ensemble) : AvgTime id ⟨fun _ => false, D⟩ := by
  refine ⟨linearFalse, ⟨fun _ _ _ => Or.inl rfl, ?_⟩⟩
  intro k n
  simp [linearFalse, Ensemble.prob, eventProb]

-- At cutoff zero, the runtime envelope still includes the empty query.
example (T : PolyTimeOracleScheme) (τ : ℕ → ℕ) (c d : ℕ) (a : Word × Accuracy) :
    T.queryTimeEnvelope τ (fun _ => 0) c d a =
      τ ((T.simulationAccuracy c d a).val + 2) := by
  simp [PolyTimeOracleScheme.queryTimeEnvelope]

-- A monotone target-time bound may be evaluated at the largest accepted size.
example (T : PolyTimeOracleScheme) (τ : ℕ → ℕ) (hτ : Monotone τ)
    (cap : Word × Accuracy → ℕ) (c d : ℕ) (a : Word × Accuracy) :
    T.queryTimeEnvelope τ cap c d a ≤ τ (cap a + (T.simulationAccuracy c d a).val + 2) :=
  T.queryTimeEnvelope_le_of_monotone τ hτ cap c d a

-- Oversized queries abort before any target execution, even for an arbitrary target function.
example (T : PolyTimeOracleScheme) (A : DeterministicScheme) (c d : ℕ) (a : Word × Accuracy) :
    T.cutoffAnswer A (fun _ => 0) c d a [true] = none := rfl

-- The accepted-query call has a genuine arbitrary-time certificate and a visible envelope.
example (T : PolyTimeOracleScheme) (τ : ℕ → ℕ)
    (A : TimeBoundedDeterministicScheme (fun a => τ ((schemeInputEncoding a).length + 1)))
    (cap : Word × Accuracy → ℕ) (hcap : ComputableTidilyInPolyTime cap schemeInputEncoding encUnary)
    (c d : ℕ) :
    ∃ e, ComputableTidilyInO
      (fun p : (Word × Accuracy) × Word => T.cutoffAnswer A.run cap c d p.1 p.2)
      (encPair schemeInputEncoding encBits) answerEncoding
      (fun p => ((encPair schemeInputEncoding encBits p).length + 1) ^ e + T.queryTimeEnvelope τ cap c d p.1)
      (fun p => ((encPair schemeInputEncoding encBits p).length + 1) ^ e + T.queryTimeEnvelope τ cap c d p.1) :=
  T.cutoffAnswer_inO τ A cap hcap c d

-- Corollary 2.2 is assembled at the computational-class level, not merely as a
-- semantic simulation plus a cost function.
example {T : PolyTimeOracleScheme} {source target : DistributionalProblem}
    (hT : ErrorlessReductionConditions T source target)
    (hsupport : T.QueriesSupported source target) (τ : ℕ → ℕ) (cap : Word × Accuracy → ℕ)
    (hcap : ComputableTidilyInPolyTime cap schemeInputEncoding encUnary)
    (bound : T.CutoffBound source target cap) (htarget : AvgTime τ target) :
    ∃ d, AvgTimeWithBound
      (fun a => ((schemeInputEncoding a).length + 1) ^ d *
        (T.queryTimeEnvelope τ cap bound.coefficient bound.degree (a.1, a.2.triple) + 1)) source :=
  hT.toAvgTimeWithBound hsupport τ cap hcap bound htarget

-- A monotone target time admits the paper-shaped factor, provided the polynomial
-- argument is explicitly enlarged rather than silently held fixed.
example {T : PolyTimeOracleScheme} {source target : DistributionalProblem}
    (hT : ErrorlessReductionConditions T source target)
    (hsupport : T.QueriesSupported source target) (τ : ℕ → ℕ) (hτ : Monotone τ)
    (cap : Word × Accuracy → ℕ) (hcap : ComputableTidilyInPolyTime cap schemeInputEncoding encUnary)
    (bound : T.CutoffBound source target cap) (htarget : AvgTime τ target) :
    ∃ (d : ℕ) (π : Word × Accuracy → ℕ),
      ComputableTidilyInPolyTime π schemeInputEncoding encUnary ∧
      (∀ a : Word × Accuracy, cap (a.1, a.2.triple) ≤ π a) ∧
      AvgTimeWithBound
        (fun a => ((schemeInputEncoding a).length + 1) ^ d * (τ (π a * a.2.val) + 1)) source :=
  hT.toAvgTimeWithBound_enlarged hsupport τ hτ cap hcap bound htarget
