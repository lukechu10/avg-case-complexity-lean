module

public import AverageCaseComplexity.Reductions.FixedBudget
public import AverageCaseComplexity.Reductions.Cutoff
public import AverageCaseComplexity.Reductions.SimulationArbitrary

@[expose] public section

namespace AverageCaseComplexity

open Turing.MultiTapeTM

/-- Unary accuracy rescaling preserves a polynomial factor times an arbitrary
input-wise cost. It does not put that arbitrary cost inside a power. -/
theorem scheme_triple_inO {f : Word × Accuracy → Answer} {H : Word × Accuracy → ℕ}
    (hf : ∃ d, ComputableTidilyInO f schemeInputEncoding answerEncoding
      (fun a => ((schemeInputEncoding a).length + 1) ^ d * (H a + 1))
      (fun a => ((schemeInputEncoding a).length + 1) ^ d * (H a + 1))) :
    ∃ d, ComputableTidilyInO (fun a : Word × Accuracy => f (a.1, a.2.triple))
      schemeInputEncoding answerEncoding
      (fun a => ((schemeInputEncoding a).length + 1) ^ d * (H (a.1, a.2.triple) + 1))
      (fun a => ((schemeInputEncoding a).length + 1) ^ d * (H (a.1, a.2.triple) + 1)) := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e, he⟩ := polytime_inO tripleInput_efficient
  let D := max e d
  have hbound : ∀ a : Word × Accuracy,
      ((schemeInputEncoding a).length + 1) ^ e +
        ((schemeInputEncoding (a.1, a.2.triple)).length + 1) ^ d * (H (a.1, a.2.triple) + 1) ≤
      (3 ^ d + 1) *
        (((schemeInputEncoding a).length + 1) ^ D * (H (a.1, a.2.triple) + 1) + 1) := by
    intro a
    have hsize : (schemeInputEncoding (a.1, a.2.triple)).length + 1 ≤
        3 * ((schemeInputEncoding a).length + 1) := by
      simp [schemeInputEncoding, Accuracy.triple]
      omega
    have hep := Nat.pow_le_pow_right (by omega : 0 < (schemeInputEncoding a).length + 1)
      (le_max_left e d)
    have hdp := Nat.pow_le_pow_right (by omega : 0 < (schemeInputEncoding a).length + 1)
      (le_max_right e d)
    have hscaled : ((schemeInputEncoding (a.1, a.2.triple)).length + 1) ^ d ≤
        3 ^ d * ((schemeInputEncoding a).length + 1) ^ D := by
      calc
        _ ≤ (3 * ((schemeInputEncoding a).length + 1)) ^ d := Nat.pow_le_pow_left hsize d
        _ = 3 ^ d * ((schemeInputEncoding a).length + 1) ^ d := Nat.mul_pow _ _ _
        _ ≤ 3 ^ d * ((schemeInputEncoding a).length + 1) ^ D := Nat.mul_le_mul_left _ hdp
    have hecost : ((schemeInputEncoding a).length + 1) ^ e ≤
        ((schemeInputEncoding a).length + 1) ^ D * (H (a.1, a.2.triple) + 1) :=
      hep.trans (Nat.le_mul_of_pos_right _ (by omega))
    calc
      _ ≤ ((schemeInputEncoding a).length + 1) ^ D * (H (a.1, a.2.triple) + 1) +
          (3 ^ d * ((schemeInputEncoding a).length + 1) ^ D) * (H (a.1, a.2.triple) + 1) :=
        Nat.add_le_add hecost (Nat.mul_le_mul_right _ hscaled)
      _ = (3 ^ d + 1) *
          (((schemeInputEncoding a).length + 1) ^ D * (H (a.1, a.2.triple) + 1)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_succ _)
  exact ⟨D, (hd.comp he).mono (3 ^ d + 1) hbound hbound⟩

namespace PolyTimeOracleScheme

/-- Largest target runtime through the cutoff, with the actual target accuracy
index left explicit. The finite envelope needs no monotonicity of `τ`. It is a
bound on machine execution, not a function the source algorithm must compute. -/
def queryTimeEnvelope (T : PolyTimeOracleScheme) (τ : ℕ → ℕ)
    (cap : Word × Accuracy → ℕ) (coefficient degree : ℕ) (a : Word × Accuracy) : ℕ :=
  (Finset.range (cap a + 1)).sup
    (fun m => τ (m + (T.simulationAccuracy coefficient degree a).val + 2))

theorem queryTimeEnvelope_le_of_monotone (T : PolyTimeOracleScheme) (τ : ℕ → ℕ)
    (hτ : Monotone τ) (cap : Word × Accuracy → ℕ) (coefficient degree : ℕ)
    (a : Word × Accuracy) :
    T.queryTimeEnvelope τ cap coefficient degree a ≤
      τ (cap a + (T.simulationAccuracy coefficient degree a).val + 2) := by
  apply Finset.sup_le
  intro m hm
  apply hτ
  have := Finset.mem_range.mp hm
  omega

/-- A cutoff target call has a real machine certificate with polynomial local
work plus the target-runtime envelope. In particular the expensive branch is
not charged at all when the query is rejected by the cutoff. -/
theorem cutoffAnswer_inO (T : PolyTimeOracleScheme) (τ : ℕ → ℕ)
    (A : TimeBoundedDeterministicScheme (fun a => τ ((schemeInputEncoding a).length + 1)))
    (cap : Word × Accuracy → ℕ)
    (hcap : ComputableTidilyInPolyTime cap schemeInputEncoding encUnary)
    (coefficient degree : ℕ) :
    ∃ d, ComputableTidilyInO
      (fun p : (Word × Accuracy) × Word => T.cutoffAnswer A.run cap coefficient degree p.1 p.2)
      (encPair schemeInputEncoding encBits) answerEncoding
      (fun p => ((encPair schemeInputEncoding encBits p).length + 1) ^ d +
        T.queryTimeEnvelope τ cap coefficient degree p.1)
      (fun p => ((encPair schemeInputEncoding encBits p).length + 1) ^ d +
        T.queryTimeEnvelope τ cap coefficient degree p.1) := by
  have hprep : ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Word =>
        (p.2, T.simulationAccuracy coefficient degree p.1))
      (encPair schemeInputEncoding encBits) schemeInputEncoding := by
    apply schemeInput_pair_efficient (ComputableTidilyInPolyTime.snd _ _)
    exact (T.simulationAccuracy_efficient coefficient degree).comp
      (ComputableTidilyInPolyTime.fst _ _)
  have hguard : ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Word => decide (p.2.length ≤ cap p.1))
      (encPair schemeInputEncoding encBits) encBool := by
    apply ComputableTidilyInPolyTime.unary_le'
    · exact (ComputableTidilyInPolyTime.encoding_length encBits).comp
        (ComputableTidilyInPolyTime.snd _ _)
    · exact hcap.comp (ComputableTidilyInPolyTime.fst _ _)
  have hnone : ComputableTidilyInPolyTime (fun _ : (Word × Accuracy) × Word => (none : Answer))
      (encPair schemeInputEncoding encBits) answerEncoding := .const none
  obtain ⟨dp, hp⟩ := polytime_inO hprep
  obtain ⟨dg, hg⟩ := polytime_inO hguard
  obtain ⟨dn, hn⟩ := polytime_inO hnone
  have hcall := A.efficient.comp hp
  have h := hg.ite hcall hn
  let D := max dg (max dp dn)
  have hcost : ∀ p : (Word × Accuracy) × Word,
      ((encPair schemeInputEncoding encBits p).length + 1) ^ dg +
        (if decide (p.2.length ≤ cap p.1) then
          ((encPair schemeInputEncoding encBits p).length + 1) ^ dp +
            τ ((schemeInputEncoding (p.2, T.simulationAccuracy coefficient degree p.1)).length + 1)
         else ((encPair schemeInputEncoding encBits p).length + 1) ^ dn) ≤
        3 * (((encPair schemeInputEncoding encBits p).length + 1) ^ D +
          T.queryTimeEnvelope τ cap coefficient degree p.1 + 1) := by
    intro p
    have hpg := Nat.pow_le_pow_right (by omega : 0 < (encPair schemeInputEncoding encBits p).length + 1)
      (le_max_left dg (max dp dn))
    have hpp := Nat.pow_le_pow_right (by omega : 0 < (encPair schemeInputEncoding encBits p).length + 1)
      ((le_max_left dp dn).trans (le_max_right dg (max dp dn)))
    have hpn := Nat.pow_le_pow_right (by omega : 0 < (encPair schemeInputEncoding encBits p).length + 1)
      ((le_max_right dp dn).trans (le_max_right dg (max dp dn)))
    by_cases hc : p.2.length ≤ cap p.1
    · have he : τ ((schemeInputEncoding (p.2, T.simulationAccuracy coefficient degree p.1)).length + 1) ≤
          T.queryTimeEnvelope τ cap coefficient degree p.1 := by
        have hh := Finset.le_sup (f := fun m => τ (m +
          (T.simulationAccuracy coefficient degree p.1).val + 2))
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hc))
        simpa [queryTimeEnvelope, schemeInputEncoding, Nat.add_assoc] using hh
      simp only [hc, decide_true, ite_true]
      dsimp [D] at *
      omega
    · simp only [hc, decide_false, Bool.false_eq_true, ite_false]
      dsimp [D] at *
      omega
  refine ⟨D, ?_⟩
  have hh := h.mono 3 hcost hcost
  exact hh.of_enc_eq (fun p => by simp [cutoffAnswer])

/-- Full arbitrary-time cutoff substitution, including the finite interpreter
loop, the target subroutine, decoding, and outer accuracy rescaling. -/
theorem cutoffSimulatedScheme_inO (T : PolyTimeOracleScheme) (τ : ℕ → ℕ)
    (A : TimeBoundedDeterministicScheme (fun a => τ ((schemeInputEncoding a).length + 1)))
    (cap : Word × Accuracy → ℕ)
    (hcap : ComputableTidilyInPolyTime cap schemeInputEncoding encUnary)
    (coefficient degree : ℕ) :
    ∃ d, ComputableTidilyInO
      (fun a : Word × Accuracy => T.cutoffSimulatedScheme A.run cap coefficient degree a.1 a.2)
      schemeInputEncoding answerEncoding
      (fun a => ((schemeInputEncoding a).length + 1) ^ d *
        (T.queryTimeEnvelope τ cap coefficient degree (a.1, a.2.triple) + 1))
      (fun a => ((schemeInputEncoding a).length + 1) ^ d *
        (T.queryTimeEnvelope τ cap coefficient degree (a.1, a.2.triple) + 1)) := by
  obtain ⟨e, he⟩ := T.cutoffAnswer_inO τ A cap hcap coefficient degree
  have hh := T.simulate_arbitrary_inO
    (answer := T.cutoffAnswer A.run cap coefficient degree) he
  exact scheme_triple_inO hh

end PolyTimeOracleScheme

/-- Quantitative heuristic transfer with the actual target accuracy left visible.
No monotonicity or regularity of the arbitrary target time function is assumed. -/
theorem HeuristicReductionConditions.toHeurTimeWithBound {T : PolyTimeOracleScheme}
    {source target : DistributionalProblem} (hT : HeuristicReductionConditions T source target)
    (τ : ℕ → ℕ) (cap : Word × Accuracy → ℕ)
    (hcap : ComputableTidilyInPolyTime cap schemeInputEncoding encUnary)
    (bound : T.CutoffBound source target cap) (htarget : HeurTime τ target) :
    ∃ d, HeurTimeWithBound
      (fun a => ((schemeInputEncoding a).length + 1) ^ d *
        (T.queryTimeEnvelope τ cap bound.coefficient bound.degree (a.1, a.2.triple) + 1)) source := by
  obtain ⟨A, hA⟩ := htarget
  obtain ⟨d, hd⟩ := T.cutoffSimulatedScheme_inO τ A cap hcap bound.coefficient bound.degree
  exact ⟨d, ⟨⟨T.cutoffSimulatedScheme A.run cap bound.coefficient bound.degree, hd⟩,
    T.cutoffSimulatedScheme_heuristic source target A.run hT.heuristic hA bound⟩⟩

/-- Corollary 2.2 with explicit target-cost envelope and support-preserving queries.
The larger accuracy argument is not silently absorbed into the outside polynomial. -/
theorem ErrorlessReductionConditions.toAvgTimeWithBound {T : PolyTimeOracleScheme}
    {source target : DistributionalProblem} (hT : ErrorlessReductionConditions T source target)
    (hsupport : T.QueriesSupported source target) (τ : ℕ → ℕ) (cap : Word × Accuracy → ℕ)
    (hcap : ComputableTidilyInPolyTime cap schemeInputEncoding encUnary)
    (bound : T.CutoffBound source target cap) (htarget : AvgTime τ target) :
    ∃ d, AvgTimeWithBound
      (fun a => ((schemeInputEncoding a).length + 1) ^ d *
        (T.queryTimeEnvelope τ cap bound.coefficient bound.degree (a.1, a.2.triple) + 1)) source := by
  obtain ⟨A, hA⟩ := htarget
  obtain ⟨d, hd⟩ := T.cutoffSimulatedScheme_inO τ A cap hcap bound.coefficient bound.degree
  exact ⟨d, ⟨⟨T.cutoffSimulatedScheme A.run cap bound.coefficient bound.degree, hd⟩,
    T.cutoffSimulatedScheme_errorless source target A.run hT.errorless hA hsupport bound⟩⟩

/-- Alternative errorless quantitative transfer using a supplied globally correct
scheme. This does not infer global correctness from AvgTime membership. -/
theorem ErrorlessReductionConditions.toAvgTimeWithBound_of_global_correct {T : PolyTimeOracleScheme}
    {source target : DistributionalProblem} (hT : ErrorlessReductionConditions T source target)
    (τ : ℕ → ℕ) (cap : Word × Accuracy → ℕ)
    (hcap : ComputableTidilyInPolyTime cap schemeInputEncoding encUnary)
    (bound : T.CutoffBound source target cap)
    (A : TimeBoundedDeterministicScheme (fun a => τ ((schemeInputEncoding a).length + 1)))
    (hA : A.run.ErrorlessConditions target) (hglobal : ∀ k y, IsAllowed target.language y (A.run y k)) :
    ∃ d, AvgTimeWithBound
      (fun a => ((schemeInputEncoding a).length + 1) ^ d *
        (T.queryTimeEnvelope τ cap bound.coefficient bound.degree (a.1, a.2.triple) + 1)) source := by
  obtain ⟨d, hd⟩ := T.cutoffSimulatedScheme_inO τ A cap hcap bound.coefficient bound.degree
  exact ⟨d, ⟨⟨T.cutoffSimulatedScheme A.run cap bound.coefficient bound.degree, hd⟩,
    T.cutoffSimulatedScheme_errorless_of_global source target A.run hT.errorless hA hglobal bound⟩⟩

/-- For monotone target time, the finite envelope can be bounded by its endpoint.
The target accuracy index remains explicit even in this specialization. -/
theorem ErrorlessReductionConditions.toAvgTimeWithBound_monotone {T : PolyTimeOracleScheme}
    {source target : DistributionalProblem} (hT : ErrorlessReductionConditions T source target)
    (hsupport : T.QueriesSupported source target) (τ : ℕ → ℕ) (hτ : Monotone τ)
    (cap : Word × Accuracy → ℕ) (hcap : ComputableTidilyInPolyTime cap schemeInputEncoding encUnary)
    (bound : T.CutoffBound source target cap) (htarget : AvgTime τ target) :
    ∃ d, AvgTimeWithBound
      (fun a => ((schemeInputEncoding a).length + 1) ^ d *
        (τ (cap (a.1, a.2.triple) +
          (T.simulationAccuracy bound.coefficient bound.degree (a.1, a.2.triple)).val + 2) + 1)) source := by
  obtain ⟨d, A, hA⟩ := hT.toAvgTimeWithBound hsupport τ cap hcap bound htarget
  refine ⟨d, ⟨⟨A.run, A.efficient.mono_le ?_ ?_⟩, hA⟩⟩
  all_goals
    intro a
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (T.queryTimeEnvelope_le_of_monotone τ hτ cap bound.coefficient bound.degree (a.1, a.2.triple)) 1)

/-- A paper-shaped bound for monotone target time, allowing an explicitly
*enlarged* polynomial argument rather than silently keeping the original cutoff.
The new argument is itself machine-computable in unary in polynomial time. -/
theorem ErrorlessReductionConditions.toAvgTimeWithBound_enlarged {T : PolyTimeOracleScheme}
    {source target : DistributionalProblem} (hT : ErrorlessReductionConditions T source target)
    (hsupport : T.QueriesSupported source target) (τ : ℕ → ℕ) (hτ : Monotone τ)
    (cap : Word × Accuracy → ℕ) (hcap : ComputableTidilyInPolyTime cap schemeInputEncoding encUnary)
    (bound : T.CutoffBound source target cap) (htarget : AvgTime τ target) :
    ∃ (d : ℕ) (π : Word × Accuracy → ℕ),
      ComputableTidilyInPolyTime π schemeInputEncoding encUnary ∧
      (∀ a : Word × Accuracy, cap (a.1, a.2.triple) ≤ π a) ∧
      AvgTimeWithBound
        (fun a => ((schemeInputEncoding a).length + 1) ^ d * (τ (π a * a.2.val) + 1)) source := by
  obtain ⟨d, A, hA⟩ := hT.toAvgTimeWithBound_monotone hsupport τ hτ cap hcap bound htarget
  let π := fun a : Word × Accuracy => cap (a.1, a.2.triple) +
    (T.simulationAccuracy bound.coefficient bound.degree (a.1, a.2.triple)).val + 2
  have hπ : ComputableTidilyInPolyTime π schemeInputEncoding encUnary := by
    have hc := hcap.comp tripleInput_efficient
    have hj := (T.simulationAccuracy_efficient bound.coefficient bound.degree).comp tripleInput_efficient
    have hsum := ComputableTidilyInPolyTime.unary_add.comp (hc.prod hj)
    exact ComputableTidilyInPolyTime.unary_add.comp (hsum.prod (.const 2))
  refine ⟨d, π, hπ, fun a => by dsimp [π]; omega, ⟨⟨A.run, ?_⟩, hA⟩⟩
  apply A.efficient.mono_le
  all_goals
    intro a
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    exact hτ (Nat.le_mul_of_pos_right (π a) a.2.property)

end AverageCaseComplexity
