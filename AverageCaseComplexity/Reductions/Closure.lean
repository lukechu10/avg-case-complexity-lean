module

public import AverageCaseComplexity.Reductions.Simulation
public import AverageCaseComplexity.Reductions.SimulationRuntime
public import AverageCaseComplexity.Reductions.QueryBounds
public import AverageCaseComplexity.Reductions.Accuracy
public import Mathlib.Tactic.Ring

@[expose] public section

namespace AverageCaseComplexity

open Turing.MultiTapeTM

/-- A union bound, stated for an arbitrary event contained in two bad events. -/
theorem eventProb_le_add {α : Type*} [Fintype α] (p : PMF α)
    {P E F : α → Prop} (h : ∀ x, P x → E x ∨ F x) :
    eventProb p P ≤ eventProb p E + eventProb p F := by
  classical
  unfold eventProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x
  · rcases h x hp with he | hf
    · simp only [ite_eq_left hp, ite_eq_left he]
      exact le_add_of_nonneg_right (by positivity)
    · simp only [ite_eq_left hp, ite_eq_left hf]
      exact le_add_of_nonneg_left (by positivity)
  · simp [hp]

namespace PolyTimeOracleScheme

/-- Polynomial query accuracy. Its size is computed solely from the encoded input length.
The +1 terms ensure positivity even for a zero domination coefficient or clock. -/
def simulationAccuracy (T : PolyTimeOracleScheme) (coefficient degree : ℕ)
    (a : Word × Accuracy) : Accuracy :=
  ⟨((schemeInputEncoding a).length + 1) *
    (coefficient * ((schemeInputEncoding a).length + 1) ^ degree + 1) *
    (T.coefficient * ((schemeInputEncoding a).length + 1) ^ T.degree + 1), by positivity⟩

/-- The accuracy budget can be computed in unary in polynomial time. -/
theorem simulationAccuracy_efficient (T : PolyTimeOracleScheme) (coefficient degree : ℕ) :
    ComputableTidilyInPolyTime (fun a => (T.simulationAccuracy coefficient degree a).val)
      schemeInputEncoding encUnary := by
  have hsize := ComputableTidilyInPolyTime.encoding_length schemeInputEncoding
  unfold simulationAccuracy
  fun_prop

/-- At a fixed source length, all queries use the same requested target accuracy. -/
theorem simulationAccuracy_eq_length (T : PolyTimeOracleScheme) (coefficient degree n : ℕ)
    (k : Accuracy) (x : Word) (hlen : x.length = n) :
    T.simulationAccuracy coefficient degree (x, k) =
      T.simulationAccuracy coefficient degree (List.replicate n false, k) := by
  apply Subtype.ext
  simp [simulationAccuracy, schemeInputEncoding, hlen]

/-- The query-length union bound consumes at most one internal accuracy budget. -/
theorem simulationAccuracy_budget (T : PolyTimeOracleScheme) (coefficient degree n : ℕ)
    (k : Accuracy) :
    (dominationFactor coefficient degree n k : ENNReal) *
      (T.coefficient * (n + k.val + 2) ^ T.degree + 1 : ℕ) *
      (T.simulationAccuracy coefficient degree ((List.replicate n false), k)).bound ≤ k.bound := by
  let C := dominationFactor coefficient degree n k
  let Q := T.coefficient * (n + k.val + 2) ^ T.degree + 1
  let j := T.simulationAccuracy coefficient degree (List.replicate n false, k)
  have hj : k.val * C * Q ≤ j.val := by
    have hj_eq : j.val = (n + k.val + 2) * (C + 1) * Q := by
      simp [j, simulationAccuracy, C, Q, dominationFactor, schemeInputEncoding, Nat.add_assoc]
    rw [hj_eq]
    exact Nat.mul_le_mul_right Q
      (Nat.mul_le_mul (by omega : k.val ≤ n + k.val + 2) (Nat.le_succ C))
  change (C : ENNReal) * (Q : ENNReal) * (j.val : ENNReal)⁻¹ ≤ (k.val : ENNReal)⁻¹
  apply ENNReal.le_inv_iff_mul_le.mpr
  calc
    (C : ENNReal) * Q * (j.val : ENNReal)⁻¹ * k.val =
        ((k.val : ENNReal) * C * Q) * (j.val : ENNReal)⁻¹ := by ac_rfl
    _ ≤ (j.val : ENNReal) * (j.val : ENNReal)⁻¹ := by
      have hcast : (k.val : ENNReal) * C * Q ≤ j.val := by exact_mod_cast hj
      simpa only [mul_comm] using mul_le_mul_right hcast (j.val : ENNReal)⁻¹
    _ = 1 := ENNReal.mul_inv_cancel (by simp [Nat.ne_of_gt j.property]) (by simp)

/-- The semantic source solver: reduce at one third of the requested outer budget,
and abort if the target solver gives up. -/
def simulatedScheme (T : PolyTimeOracleScheme) (A : DeterministicScheme)
    (coefficient degree : ℕ) : DeterministicScheme := fun x k =>
  T.simulate (fun a y => A y (T.simulationAccuracy coefficient degree a)) (x, k.triple)

/-- The distributional part of heuristic closure. No runtime certificate is
inferred from this theorem; machine-level simulation is a separate obligation. -/
theorem simulatedScheme_heuristic (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : DeterministicScheme)
    (hT : (T.run target.language).HeuristicConditions source)
    (hA : A.HeuristicConditions target) (coefficient degree : ℕ)
    (hdom : ∀ k n, ∃ E : Set (FixedWord n),
      eventProb (source.distribution n) E ≤ k.bound ∧
      ∀ y, T.queryMass target.language source.distribution k n E y ≤
        (dominationFactor coefficient degree n k : ENNReal) * target.distribution.wordMass y) :
    (T.simulatedScheme A coefficient degree).HeuristicConditions source := by
  classical
  intro k n
  let u := k.triple
  let j := T.simulationAccuracy coefficient degree (List.replicate n false, u)
  let bad : Word → Prop := fun y => A y j ≠ some (target.language y)
  obtain ⟨E, hE, hEy⟩ := hdom u n
  let fails : FixedWord n → Prop := fun w =>
    T.run target.language w.toWord u ≠ some (source.language w.toWord)
  let queryBad : FixedWord n → Prop := fun w =>
    w ∉ E ∧ ∃ y, T.Asks target.language w.toWord u y ∧ bad y
  have hcontain : ∀ w : FixedWord n,
      T.simulatedScheme A coefficient degree w.toWord k ≠ some (source.language w.toWord) →
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
    have hacc := T.simulationAccuracy_eq_length coefficient degree n u w.toWord (by simp)
    have heq := T.simulate_eq_of_answers target.language
      (fun a y => A y (T.simulationAccuracy coefficient degree a)) (w.toWord, u) (by
        intro y hy
        rw [hacc]
        exact not_ne_iff.mp (fun hb => hno ⟨y, hy, hb⟩))
    change T.simulate _ (w.toWord, u) ≠ _ at hw
    rw [heq] at hw
    exact hw (not_ne_iff.mp hf)
  have hquery : eventProb (source.distribution n) queryBad ≤ u.bound := by
    have hq := badQueryEventProb_le T source target u n E
      (dominationFactor coefficient degree n u) j.bound hEy bad (by
        intro m hm
        exact (hA j m).le)
    exact hq.trans (T.simulationAccuracy_budget coefficient degree n u)
  have hunion : eventProb (source.distribution n) (fun w => w ∈ E ∨ queryBad w) ≤
      u.bound + u.bound := by
    exact (eventProb_le_add (source.distribution n) (fun _ h => h)).trans
      (add_le_add hE hquery)
  have hthree : u.bound + (u.bound + u.bound) = k.bound := by
    calc
      _ = 3 * k.triple.bound := by change k.triple.bound + _ = _; ring
      _ = k.bound := by
        rw [Accuracy.triple_bound, div_eq_mul_inv, mul_left_comm]
        simp [ENNReal.mul_inv_cancel (by norm_num : (3 : ENNReal) ≠ 0) (by simp)]
  calc
    source.distribution.prob n
        (fun x => T.simulatedScheme A coefficient degree x k ≠ some (source.language x))
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

/-- Pointwise errorlessness needs support preservation on *all* supported inputs,
including those in domination's exceptional set. This is an explicit extra hypothesis. -/
theorem simulatedScheme_correct (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : DeterministicScheme)
    (hT : (T.run target.language).Correct source) (hA : A.Correct target)
    (hsupport : T.QueriesSupported source target) (coefficient degree : ℕ) :
    (T.simulatedScheme A coefficient degree).Correct source := by
  intro k x hx
  have hh := T.simulate_eq_none_or_run target.language
    (fun a y => A y (T.simulationAccuracy coefficient degree a)) (x, k.triple) (by
      intro y hy
      exact hA _ y (hsupport k.triple x hx y hy))
  rcases hh with hh | hh
  · exact Or.inr hh
  · change IsAllowed source.language x (T.simulate _ (x, k.triple))
    rw [hh]
    exact hT k.triple x hx

/-- Semantic errorless closure with the explicitly stated support-preservation repair. -/
theorem simulatedScheme_errorless (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : DeterministicScheme)
    (hT : (T.run target.language).ErrorlessConditions source)
    (hA : A.ErrorlessConditions target) (hsupport : T.QueriesSupported source target)
    (coefficient degree : ℕ)
    (hdom : ∀ k n, ∃ E : Set (FixedWord n),
      eventProb (source.distribution n) E ≤ k.bound ∧
      ∀ y, T.queryMass target.language source.distribution k n E y ≤
        (dominationFactor coefficient degree n k : ENNReal) * target.distribution.wordMass y) :
    (T.simulatedScheme A coefficient degree).ErrorlessConditions source := by
  constructor
  · exact T.simulatedScheme_correct source target A hT.correct hA.correct hsupport
      coefficient degree
  · have hh := T.simulatedScheme_heuristic source target A hT.toHeuristic hA.toHeuristic
      coefficient degree hdom
    intro k n
    apply lt_of_le_of_lt (source.distribution.prob_mono_on_support n ?_) (hh k n)
    intro x hx hnone
    rw [hnone]
    simp

/-- Alternative errorless repair: the target solver is correct or gives up on
all words, including words outside target support. -/
theorem simulatedScheme_correct_of_global (T : PolyTimeOracleScheme)
    (source target : DistributionalProblem) (A : DeterministicScheme)
    (hT : (T.run target.language).Correct source)
    (hglobal : ∀ k y, IsAllowed target.language y (A y k)) (coefficient degree : ℕ) :
    (T.simulatedScheme A coefficient degree).Correct source := by
  intro k x hx
  have hh := T.simulate_eq_none_or_run target.language
    (fun a y => A y (T.simulationAccuracy coefficient degree a)) (x, k.triple)
    (fun y _ => hglobal _ y)
  rcases hh with hh | hh
  · exact Or.inr hh
  · change IsAllowed source.language x (T.simulate _ (x, k.triple))
    rw [hh]
    exact hT k.triple x hx

/-- The target-solver call, including construction of its unary accuracy input,
is a certified polynomial-time function of the source input and the query. -/
theorem simulationHandler_efficient (T : PolyTimeOracleScheme)
    (A : PolyTimeDeterministicScheme) (coefficient degree : ℕ) :
    ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Word => A.run p.2
        (T.simulationAccuracy coefficient degree p.1))
      (encPair schemeInputEncoding encBits) answerEncoding := by
  have hprep : ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Word =>
        (p.2, T.simulationAccuracy coefficient degree p.1))
      (encPair schemeInputEncoding encBits) schemeInputEncoding := by
    apply schemeInput_pair_efficient (ComputableTidilyInPolyTime.snd _ _)
    exact (T.simulationAccuracy_efficient coefficient degree).comp
      (ComputableTidilyInPolyTime.fst _ _)
  exact A.efficient.comp hprep

/-- A machine-certified composition, with all oracle failures propagated as give-up. -/
def compose (T : PolyTimeOracleScheme) (A : PolyTimeDeterministicScheme)
    (coefficient degree : ℕ) : PolyTimeDeterministicScheme where
  run := T.simulatedScheme A.run coefficient degree
  efficient := by
    have hh := (T.simulate_efficient
      (answer := fun a y => A.run y (T.simulationAccuracy coefficient degree a))
      (T.simulationHandler_efficient A coefficient degree)).comp
      tripleInput_efficient
    exact hh

end PolyTimeOracleScheme

/-- Heuristic reductions preserve `HeurP` (Itsykson Lemma 2.2(2)). -/
theorem HeuristicReductionConditions.toHeurP {T : PolyTimeOracleScheme}
    {source target : DistributionalProblem} (hT : HeuristicReductionConditions T source target)
    (htarget : HeurP target) : HeurP source := by
  obtain ⟨A, hA⟩ := htarget
  obtain ⟨coefficient, degree, hdom⟩ := hT.domination
  exact ⟨T.compose A coefficient degree,
    T.simulatedScheme_heuristic source target A.run hT.heuristic hA coefficient degree hdom⟩

/-- The class-level downward closure theorem for heuristic reducibility. -/
theorem HeuristicallyReducible.toHeurP {source target : DistributionalProblem}
    (hred : HeuristicallyReducible source target) (htarget : HeurP target) : HeurP source := by
  obtain ⟨T, hT⟩ := hred
  exact hT.toHeurP htarget

/-- Errorless closure with an explicit support-preservation hypothesis.
The hypothesis is not silently included in `ErrorlesslyReducible`: domination
alone gives support preservation only outside its exceptional set. -/
theorem ErrorlessReductionConditions.toAvgP {T : PolyTimeOracleScheme}
    {source target : DistributionalProblem} (hT : ErrorlessReductionConditions T source target)
    (hsupport : T.QueriesSupported source target) (htarget : AvgP target) : AvgP source := by
  obtain ⟨A, hA⟩ := htarget
  obtain ⟨coefficient, degree, hdom⟩ := hT.domination
  exact ⟨T.compose A coefficient degree,
    T.simulatedScheme_errorless source target A.run hT.errorless hA hsupport
      coefficient degree hdom⟩

/-- Errorless closure also holds for a supplied target solver that is globally
correct-or-give-up. Global correctness is explicit and is not inferred from `AvgP`. -/
theorem ErrorlessReductionConditions.toAvgP_of_global_correct {T : PolyTimeOracleScheme}
    {source target : DistributionalProblem} (hT : ErrorlessReductionConditions T source target)
    (A : PolyTimeDeterministicScheme) (hA : A.run.ErrorlessConditions target)
    (hglobal : ∀ k y, IsAllowed target.language y (A.run y k)) : AvgP source := by
  obtain ⟨coefficient, degree, hdom⟩ := hT.domination
  refine ⟨T.compose A coefficient degree, ?_⟩
  constructor
  · exact T.simulatedScheme_correct_of_global source target A.run hT.errorless.correct
      hglobal coefficient degree
  · have hh := T.simulatedScheme_heuristic source target A.run hT.errorless.toHeuristic
      hA.toHeuristic coefficient degree hdom
    intro k n
    apply lt_of_le_of_lt (source.distribution.prob_mono_on_support n ?_) (hh k n)
    intro x hx hnone
    change T.simulatedScheme A.run coefficient degree x k = none at hnone
    rw [hnone]
    simp

/-- In particular, the extra hypothesis is automatic for a fully supported target ensemble. -/
theorem ErrorlesslyReducible.toAvgP_of_fullSupport {source target : DistributionalProblem}
    (hred : ErrorlesslyReducible source target)
    (hfull : ∀ y, target.distribution.Supports y) (htarget : AvgP target) : AvgP source := by
  obtain ⟨T, hT⟩ := hred
  exact hT.toAvgP (fun _ _ _ y _ => hfull y) htarget

end AverageCaseComplexity
