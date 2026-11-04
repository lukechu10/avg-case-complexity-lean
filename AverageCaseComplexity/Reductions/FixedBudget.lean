module

public import AverageCaseComplexity.FixedBudget
public import AverageCaseComplexity.Reductions.Closure
public import AverageCaseComplexity.Reductions.QueryLengthBounds

/-!
# Fixed-budget targets (Itsykson, Corollary 2.1)

A fixed target algorithm suffices if its length-dependent error budget is at
most the simulation's requested budget on every true-oracle query. This is
stated for arbitrary budgets; inverse-polynomial error is a specialization.
The errorless fixed-budget algorithm is globally correct-or-give-up, as in
Section 2.4, so this corollary does not require unrestricted errorless closure.
-/

@[expose] public section

namespace AverageCaseComplexity

open Turing.MultiTapeTM

namespace PolyTimeOracleScheme

/-- Accuracy derived from the *number of distinct query lengths*, not their
maximum. This distinction is essential for padding with inverse-polynomial errors. -/
def fixedBudgetAccuracy (coefficient degree n : ℕ) (k : Accuracy) (count : ℕ) : Accuracy :=
  ⟨(n + k.val + 2) * (dominationFactor coefficient degree n k + 1) * (count + 1), by positivity⟩

/-- If the length-count majorant is efficiently available, its requested unary
accuracy is too. Fixed target simulation itself does not need to compute it. -/
theorem fixedBudgetAccuracy_efficient (coefficient degree : ℕ)
    {count : Word × Accuracy → ℕ}
    (hcount : ComputableTidilyInPolyTime count schemeInputEncoding encUnary) :
    ComputableTidilyInPolyTime
      (fun a : Word × Accuracy =>
        (fixedBudgetAccuracy coefficient degree a.1.length a.2 (count a)).val)
      schemeInputEncoding encUnary := by
  have hlen := (ComputableTidilyInPolyTime.encoding_length encBits).comp schemeInput_word_efficient
  have hindex := schemeInput_index_efficient
  change ComputableTidilyInPolyTime
    (fun a : Word × Accuracy =>
      (a.1.length + a.2.val + 2) *
        (coefficient * (a.1.length + a.2.val + 2) ^ degree + 1) * (count a + 1))
    schemeInputEncoding encUnary
  fun_prop

theorem fixedBudgetAccuracy_budget (coefficient degree n : ℕ) (k : Accuracy) (count : ℕ) :
    (dominationFactor coefficient degree n k : ENNReal) * (count : ENNReal) *
      (fixedBudgetAccuracy coefficient degree n k count).bound ≤ k.bound := by
  let C := dominationFactor coefficient degree n k
  let j := fixedBudgetAccuracy coefficient degree n k count
  have hj : k.val * C * count ≤ j.val := by
    change k.val * C * count ≤ (n + k.val + 2) * (C + 1) * (count + 1)
    exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (Nat.le_succ C)) (Nat.le_succ count)
  change (C : ENNReal) * count * (j.val : ENNReal)⁻¹ ≤ (k.val : ENNReal)⁻¹
  apply ENNReal.le_inv_iff_mul_le.mpr
  calc
    (C : ENNReal) * count * (j.val : ENNReal)⁻¹ * k.val =
        ((k.val : ENNReal) * C * count) * (j.val : ENNReal)⁻¹ := by ac_rfl
    _ ≤ (j.val : ENNReal) * (j.val : ENNReal)⁻¹ := by
      have hcast : (k.val : ENNReal) * C * count ≤ j.val := by exact_mod_cast hj
      simpa only [mul_comm] using mul_le_mul_right hcast (j.val : ENNReal)⁻¹
    _ = 1 := ENNReal.mul_inv_cancel (by simp [Nat.ne_of_gt j.property]) (by simp)

/-- A particular domination majorant together with the query-length budget
condition. Unlike a bare existential domination witness, the two fields use
the same coefficients. No effectiveness assumption on the error function is needed. -/
structure FixedBudgetBound (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (η : ℕ → ENNReal) where
  coefficient : ℕ
  degree : ℕ
  lengthCount : ℕ → Accuracy → ℕ
  length_cover : ∀ k n, ∃ lengths : Finset ℕ, lengths.card ≤ lengthCount n k ∧
    ∀ w : FixedWord n, ∀ y, T.Asks target.language w.toWord k y → y.length ∈ lengths
  domination : ∀ k n, ∃ E : Set (FixedWord n),
    eventProb (source.distribution n) E ≤ k.bound ∧
    ∀ y, T.queryMass target.language source.distribution k n E y ≤
      (dominationFactor coefficient degree n k : ENNReal) * target.distribution.wordMass y
  query_budget : ∀ k x y, T.Asks target.language x k y →
    η y.length ≤ (fixedBudgetAccuracy coefficient degree x.length k (lengthCount x.length k)).bound

/-- The paper's lower bound on query length, expressed without rounding roots:
`j ≤ |y|^c` implies that target error `|y|⁻ᶜ` is at most `1/j`.
The arbitrary-budget theorem below also permits nonintegral exponents. -/
def FixedBudgetBound.of_inversePolynomial (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (c coefficient degree : ℕ)
    (lengthCount : ℕ → Accuracy → ℕ)
    (hcover : ∀ k n, ∃ lengths : Finset ℕ, lengths.card ≤ lengthCount n k ∧
      ∀ w : FixedWord n, ∀ y, T.Asks target.language w.toWord k y → y.length ∈ lengths)
    (hdom : ∀ k n, ∃ E : Set (FixedWord n),
      eventProb (source.distribution n) E ≤ k.bound ∧
      ∀ y, T.queryMass target.language source.distribution k n E y ≤
        (dominationFactor coefficient degree n k : ENNReal) * target.distribution.wordMass y)
    (hlength : ∀ k x y, T.Asks target.language x k y →
      (fixedBudgetAccuracy coefficient degree x.length k (lengthCount x.length k)).val ≤ y.length ^ c) :
    T.FixedBudgetBound source target (inversePolynomialError c) where
  coefficient := coefficient
  degree := degree
  lengthCount := lengthCount
  length_cover := hcover
  domination := hdom
  query_budget := fun k x y hy => inversePolynomialError_le_bound (hlength k x y hy)

/-- Real-exponent specialization. For positive `c` the hypothesis is the
root-free form of the paper's rounded lower bound on query length. -/
def FixedBudgetBound.of_inversePower (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (c : ℝ) (coefficient degree : ℕ)
    (lengthCount : ℕ → Accuracy → ℕ)
    (hcover : ∀ k n, ∃ lengths : Finset ℕ, lengths.card ≤ lengthCount n k ∧
      ∀ w : FixedWord n, ∀ y, T.Asks target.language w.toWord k y → y.length ∈ lengths)
    (hdom : ∀ k n, ∃ E : Set (FixedWord n),
      eventProb (source.distribution n) E ≤ k.bound ∧
      ∀ y, T.queryMass target.language source.distribution k n E y ≤
        (dominationFactor coefficient degree n k : ENNReal) * target.distribution.wordMass y)
    (hlength : ∀ k x y, T.Asks target.language x k y →
      ((fixedBudgetAccuracy coefficient degree x.length k (lengthCount x.length k)).val : ENNReal) ≤
        (y.length : ENNReal) ^ c) :
    T.FixedBudgetBound source target (inversePowerError c) where
  coefficient := coefficient
  degree := degree
  lengthCount := lengthCount
  length_cover := hcover
  domination := hdom
  query_budget := fun k x y hy => inversePowerError_le_bound (hlength k x y hy)

/-- Execute the reduction at one third of the outer budget, using a target
algorithm with no adjustable accuracy argument. -/
def fixedSimulatedScheme (T : PolyTimeOracleScheme) (A : FixedAlgorithm) : DeterministicScheme :=
  fun x k => T.simulate (fun _ y => A y) (x, k.triple)

/-- The actual composed deterministic polynomial-time algorithm. -/
def fixedCompose (T : PolyTimeOracleScheme) (A : PolyTimeDeterministicAlgorithm) :
    PolyTimeDeterministicScheme where
  run := T.fixedSimulatedScheme A.run
  efficient := (T.simulate_efficient (answer := fun _ y => A.run y)
    (A.efficient.comp (ComputableTidilyInPolyTime.snd _ _))).comp tripleInput_efficient

/-- General fixed-budget transfer. Masking the bad-query predicate by its length
budget avoids assuming target accuracy at lengths the reduction never queries. -/
theorem fixedSimulatedScheme_heuristic (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : FixedAlgorithm) (η : ℕ → ENNReal)
    (hT : (T.run target.language).HeuristicConditions source)
    (hA : A.HeuristicConditions target η) (bound : T.FixedBudgetBound source target η) :
    (T.fixedSimulatedScheme A).HeuristicConditions source := by
  classical
  intro k n
  let u := k.triple
  let j := fixedBudgetAccuracy bound.coefficient bound.degree n u (bound.lengthCount n u)
  let bad : Word → Prop := fun y => A y ≠ some (target.language y) ∧ η y.length ≤ j.bound
  obtain ⟨E, hE, hEy⟩ := bound.domination u n
  let fails : FixedWord n → Prop := fun w =>
    T.run target.language w.toWord u ≠ some (source.language w.toWord)
  let queryBad : FixedWord n → Prop := fun w =>
    w ∉ E ∧ ∃ y, T.Asks target.language w.toWord u y ∧ bad y
  have hcontain : ∀ w : FixedWord n,
      T.fixedSimulatedScheme A w.toWord k ≠ some (source.language w.toWord) →
      fails w ∨ (w ∈ E ∨ queryBad w) := by
    intro w hw
    by_cases hf : fails w
    · exact Or.inl hf
    right
    by_cases he : w ∈ E
    · exact Or.inl he
    right
    refine ⟨he, ?_⟩
    by_contra hno
    have heq := T.simulate_eq_of_answers target.language (fun _ y => A y) (w.toWord, u) (by
      intro y hy
      apply not_ne_iff.mp
      intro hb
      have hbudget := bound.query_budget u w.toWord y hy
      exact hno ⟨y, hy, hb, by simpa using hbudget⟩)
    change T.simulate _ (w.toWord, u) ≠ _ at hw
    rw [heq] at hw
    exact hw (not_ne_iff.mp hf)
  have hbad : ∀ m, target.distribution.prob m bad ≤ j.bound := by
    intro m
    by_cases hm : η m ≤ j.bound
    · apply le_trans (target.distribution.prob_mono_on_support m ?_) ((hA m).le.trans hm)
      intro y hy hb
      exact hb.1
    · have hz : target.distribution.prob m bad = 0 := by
        unfold Ensemble.prob eventProb
        apply Finset.sum_eq_zero
        intro w _
        have hnb : ¬ bad w.toWord := by
          intro hb
          exact hm (by simpa using hb.2)
        simp [hnb]
      rw [hz]
      exact bot_le
  have hquery : eventProb (source.distribution n) queryBad ≤ u.bound := by
    obtain ⟨lengths, hcard, hcover⟩ := bound.length_cover u n
    have hq := badQueryEventProb_le_cover T source target u n E
      (dominationFactor bound.coefficient bound.degree n u) j.bound lengths hcover hEy bad
      (fun m _ => hbad m)
    have hcard' : (lengths.card : ENNReal) ≤ bound.lengthCount n u := by exact_mod_cast hcard
    calc
      _ ≤ (dominationFactor bound.coefficient bound.degree n u : ENNReal) * lengths.card * j.bound := hq
      _ ≤ (dominationFactor bound.coefficient bound.degree n u : ENNReal) *
          (bound.lengthCount n u : ENNReal) * j.bound := by gcongr
      _ ≤ u.bound := fixedBudgetAccuracy_budget bound.coefficient bound.degree n u (bound.lengthCount n u)
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
        (fun x => T.fixedSimulatedScheme A x k ≠ some (source.language x))
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

/-- Global correctness of the fixed target algorithm handles exceptional source
inputs as well, without a support-preservation assumption. -/
theorem fixedSimulatedScheme_correct (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : FixedAlgorithm)
    (hT : (T.run target.language).Correct source)
    (hA : ∀ y, IsAllowed target.language y (A y)) :
    (T.fixedSimulatedScheme A).Correct source := by
  intro k x hx
  have hh := T.simulate_eq_none_or_run target.language (fun _ y => A y) (x, k.triple)
    (fun y _ => hA y)
  rcases hh with hh | hh
  · exact Or.inr hh
  · change IsAllowed source.language x (T.simulate _ (x, k.triple))
    rw [hh]
    exact hT k.triple x hx

end PolyTimeOracleScheme

/-- Corollary 2.1(2): sufficiently long queries turn a fixed-budget polynomial-time
heuristic target algorithm into a heuristic scheme for the source. -/
theorem HeuristicReductionConditions.toHeurP_of_fixedBudget {T : PolyTimeOracleScheme}
    {source target : DistributionalProblem} (hT : HeuristicReductionConditions T source target)
    {η : ℕ → ENNReal} (bound : T.FixedBudgetBound source target η)
    (htarget : HeurFixedP η target) : HeurP source := by
  obtain ⟨A, hA⟩ := htarget
  exact ⟨T.fixedCompose A, T.fixedSimulatedScheme_heuristic source target A.run η hT.heuristic hA bound⟩

/-- Corollary 2.1(1): the fixed-budget errorless definition is globally correct,
so this statement does not depend on the deferred unrestricted AvgP closure. -/
theorem ErrorlessReductionConditions.toAvgP_of_fixedBudget {T : PolyTimeOracleScheme}
    {source target : DistributionalProblem} (hT : ErrorlessReductionConditions T source target)
    {η : ℕ → ENNReal} (bound : T.FixedBudgetBound source target η)
    (htarget : AvgFixedP η target) : AvgP source := by
  obtain ⟨A, hA⟩ := htarget
  refine ⟨T.fixedCompose A, ?_, ?_⟩
  · exact T.fixedSimulatedScheme_correct source target A.run hT.errorless.correct hA.correct
  · have hh := T.fixedSimulatedScheme_heuristic source target A.run η hT.errorless.toHeuristic
      hA.toHeuristic bound
    intro k n
    apply lt_of_le_of_lt (source.distribution.prob_mono_on_support n ?_) (hh k n)
    intro x hx hnone
    change T.fixedSimulatedScheme A.run x k = none at hnone
    rw [hnone]
    simp

end AverageCaseComplexity
