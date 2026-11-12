module

public import AverageCaseComplexity.Completeness.AnswerLaw
public import AverageCaseComplexity.Reductions.Closure
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# Itsykson's two-query complete problem (§3, Theorems 3.1–3.2), in progress

This is NOT a completed formalization. Foundational theorems and executable
constructions still have explicit `sorry` bodies. Conditional reduction proofs
and final assembly do not remove those dependencies. In particular, the
universal interpreter and its compilers must ultimately use the library's
finite-control fair-coin machines, not arbitrary PMFs supplied with an asserted
running time. The separate `AnswerLaw` module has no placeholders.

Dependency order:
1. binary machine codes and logarithmic-overhead tuple encoding;
2. the language C and elementary probability facts;
3. Algorithm 3.1, its strict runtime, and Lemma 3.2's mass bounds;
4. Lemma 3.1 and target membership (Theorem 3.1);
5. amplified/compiled source witnesses and query generation;
6. uniform-clock two-query execution, correctness, usefulness, domination;
7. completeness (Theorem 3.2).

We use reciprocal accuracy k and size n+k+2, including n=0. Malformed words
are rejected by C. Sampler outputs are normalized to the requested length;
this is necessary for our length-indexed Ensemble API. The tuple encoding may
use a different binary self-delimiting convention from the paper, but must
have logarithmic overhead (unary separators would destroy domination).
-/

namespace AverageCaseComplexity.Completeness.TwoQuery

/-! ## 1. Machine codes, bounded execution, and tuple encoding -/

/-- Must be implemented by decoding and running an actual fair-coin machine.
Invalid codes have a fixed give-up interpretation. -/
noncomputable def boundedAnswer (code : Word) (steps : ℕ) (x : Word) : PMF Answer := by
  sorry

/-- Bounded sampler semantics, truncating/padding the output to exactly n bits.
The same normalization must be used in the executable universal simulator. -/
noncomputable def boundedSample (code : Word) (steps n : ℕ) : PMF (FixedWord n) := by
  sorry

/-- This branch will compute C's bit, not merely one sample of boundedAnswer.
The concrete implementation enumerates at most 2^steps coin strings. -/
def exactLanguageBit (code : Word) (steps : ℕ) (x : Word) (fallback : Bool) : Bool := by
  sorry

/-- A conservative choice of the paper's N₀; only its inequalities matter. -/
def burnIn : ℕ := 10000

theorem burnIn_tail :
    2 * Real.exp (-(burnIn : ℝ) / 1000) < (1 / 1000 : ℝ) := by
  sorry

/-- Canonical query tuple (M,x,1^m,b,S,1^s). Validity is separate. -/
structure Instance where
  machineCode : Word
  input : Word
  steps : ℕ
  fallback : Bool
  samplerCode : Word
  samplerSteps : ℕ

/-- Raw seed tuple (M,y,r,b,S,σ) in Algorithm 3.1, before canonicalization. -/
structure Seed where
  machineCode : Word
  input : Word
  clockBits : Word
  fallback : Bool
  samplerCode : Word
  samplerClockBits : Word

def Instance.Valid (z : Instance) : Prop := z.input.length + burnIn < z.steps

def encodeSeed (z : Seed) : Word := by
  sorry

def decodeSeed (w : Word) : Option Seed := by
  sorry

def Instance.seed (z : Instance) : Seed :=
  ⟨z.machineCode, z.input, List.replicate z.steps true, z.fallback,
    z.samplerCode, List.replicate z.samplerSteps true⟩

def encode (z : Instance) : Word := encodeSeed z.seed

/-- Parses only canonical unary-clock tuples; it need not check Valid. -/
def decode (w : Word) : Option Instance := by
  sorry

theorem decodeSeed_encodeSeed (z : Seed) : decodeSeed (encodeSeed z) = some z := by
  sorry

theorem decode_encode (z : Instance) : decode (encode z) = some z := by
  sorry

theorem encode_injective : Function.Injective encode := by
  sorry

/-- The all-ones rejection word cannot contribute mass to any encoded tuple. -/
theorem decodeSeed_ones (n : ℕ) : decodeSeed (List.replicate n true) = none := by
  sorry

/-- Encoding length depends on component lengths, not their contents. -/
theorem encodeSeed_length_congr (u v : Seed)
    (hM : u.machineCode.length = v.machineCode.length)
    (hx : u.input.length = v.input.length)
    (hm : u.clockBits.length = v.clockBits.length)
    (hS : u.samplerCode.length = v.samplerCode.length)
    (hs : u.samplerClockBits.length = v.samplerClockBits.length) :
    (encodeSeed u).length = (encodeSeed v).length := by
  sorry

/-- Coarse integer version of Remark 3.1, sufficient for polynomial domination. -/
theorem encodeSeed_length_le (z : Seed) :
    (encodeSeed z).length ≤
      z.machineCode.length + z.input.length + z.clockBits.length + 1 +
      z.samplerCode.length + z.samplerClockBits.length +
      10 * (Nat.log2 (z.machineCode.length + z.input.length +
        z.clockBits.length + z.samplerCode.length + 2) + 1) + 5 := by
  sorry

theorem payload_length_le_encode_length (z : Instance) :
    z.machineCode.length + z.input.length + z.steps + 1 +
      z.samplerCode.length + z.samplerSteps ≤ (encode z).length := by
  sorry

theorem input_length_le_encode_length (z : Instance) :
    z.input.length ≤ (encode z).length := by
  sorry

/-! ## 2. The complete language and its two-answer truth table -/

noncomputable def instanceBit (z : Instance) : Bool :=
  if (1 / 4 : ENNReal) ≤ boundedAnswer z.machineCode z.steps z.input none
    then z.fallback
    else frequentBit (boundedAnswer z.machineCode z.steps z.input)

open scoped Classical in
/-- C rejects malformed tuples and tuples whose clock is too short. -/
noncomputable def language (w : Word) : Bool :=
  match decode w with
  | none => false
  | some z => if z.Valid then instanceBit z else false

theorem language_encode (z : Instance) (hz : z.Valid) :
    language (encode z) = instanceBit z := by
  simp [language, decode_encode, hz]

theorem exactLanguageBit_eq (z : Instance) :
    exactLanguageBit z.machineCode z.steps z.input z.fallback = instanceBit z := by
  sorry

/-- The only difference between the two instances is the fallback bit. -/
theorem query_answers_differ_iff (z : Instance) (hz : z.Valid) :
    language (encode { z with fallback := false }) ≠
      language (encode { z with fallback := true }) ↔
    (1 / 4 : ENNReal) ≤ boundedAnswer z.machineCode z.steps z.input none := by
  rw [language_encode _ (show ({z with fallback := false}).Valid from hz),
    language_encode _ (show ({z with fallback := true}).Valid from hz)]
  by_cases h : (1 / 4 : ENNReal) ≤ boundedAnswer z.machineCode z.steps z.input none
  · simpa only [instanceBit, h, if_pos] using (show (false ≠ true ↔ True) by simp)
  · simp only [instanceBit, h, if_false, ne_eq, not_true_eq_false]

/-! ## 3. Algorithm 3.1 and the mass estimates (Lemma 3.2) -/

noncomputable def tailBound (n : ℕ) : ENNReal :=
  ENNReal.ofReal (2 * Real.exp (-((n : ℝ) ^ 2)))

/-- Sample the bounded computation independently 200*N^2 times; accept iff
one Boolean answer occupies at least 90% of the samples. -/
def reliabilityTest (code : Word) (steps : ℕ) (x : Word) (N : ℕ) :
    Cslib.ProbComp Bool := by
  sorry

theorem reliabilityTest_accept_lower (code : Word) (steps : ℕ) (x : Word) (N : ℕ)
    (hN : 0 < N)
    (hgood : (95 / 100 : ENNReal) ≤ peak (boundedAnswer code steps x)) :
    1 - tailBound N ≤ Cslib.ProbComp.eval (reliabilityTest code steps x N) true := by
  sorry

theorem reliabilityTest_accept_upper (code : Word) (steps : ℕ) (x : Word) (N : ℕ)
    (hbad : peak (boundedAnswer code steps x) ≤ (85 / 100 : ENNReal)) :
    Cslib.ProbComp.eval (reliabilityTest code steps x N) true ≤ tailBound N := by
  sorry

/-- Algorithm 3.1: uniform seed, bounded normalized sampling, reliability filter,
canonical tuple on success, all-ones on failure; unparseable seeds are unchanged. -/
def sampler (n : ℕ) : Cslib.ProbComp Word := by
  sorry

/-- The semantic step-by-step specification must be proved for the implementation. -/
noncomputable def samplerLaw (n : ℕ) : PMF Word :=
  (uniformEnsemble.wordDistribution n).bind fun w =>
    match decodeSeed w with
    | none => PMF.pure w
    | some z => (boundedSample z.samplerCode z.samplerClockBits.length z.input.length).bind
        fun x => (Cslib.ProbComp.eval
          (reliabilityTest z.machineCode z.clockBits.length x.toWord n)).map fun accept =>
            if accept then encode ⟨z.machineCode, x.toWord, z.clockBits.length,
              z.fallback, z.samplerCode, z.samplerClockBits.length⟩
            else List.replicate n true

theorem sampler_eval (n : ℕ) : Cslib.ProbComp.eval (sampler n) = samplerLaw n := by
  sorry

theorem sampler_output_length (n : ℕ) (w : Word)
    (hw : Cslib.ProbComp.eval (sampler n) w ≠ 0) : w.length = n := by
  sorry

theorem sampler_efficient :
    Cslib.Probability.IsPPTOn unaryEncoding (Function.Embedding.refl Word) sampler := by
  sorry

/-- Construct the fixed-length PMF using sampler_output_length. -/
noncomputable def distribution : Ensemble := by
  sorry

theorem distribution_wordDistribution (n : ℕ) :
    distribution.wordDistribution n = Cslib.ProbComp.eval (sampler n) := by
  sorry

theorem distribution_psamp : PSamp distribution := by
  sorry

/-- Coarse replacement for the paper's logarithmic/exponential prefactor.
The factor is deliberately weaker, avoiding real-valued logarithms. -/
def seedDenominator (z : Instance) : ℕ :=
  2 ^ 20 * ((encode z).length + 1) ^ 10 *
    2 ^ (z.machineCode.length + z.samplerCode.length)

/-- Uniform seed mass of the entire fiber of irrelevant y,r,σ bits.
Counting just one seed would introduce an exponential loss in input length. -/
theorem seed_fiber_mass_lower (z : Instance) :
    (seedDenominator z : ENNReal)⁻¹ ≤
      eventProb (uniformEnsemble (encode z).length) (fun w =>
        ∃ u, decodeSeed w.toWord = some u ∧
          u.machineCode = z.machineCode ∧ u.input.length = z.input.length ∧
          u.clockBits.length = z.steps ∧ u.fallback = z.fallback ∧
          u.samplerCode = z.samplerCode ∧ u.samplerClockBits.length = z.samplerSteps) := by
  sorry

/-- Lemma 3.2(1), with a coarse polynomial encoding prefactor. -/
theorem distribution_mass_lower (z : Instance) (hz : z.Valid)
    (hgood : (95 / 100 : ENNReal) ≤ peak (boundedAnswer z.machineCode z.steps z.input)) :
    (1 - tailBound (encode z).length) *
        (boundedSample z.samplerCode z.samplerSteps z.input.length).map
          FixedWord.toWord z.input * (seedDenominator z : ENNReal)⁻¹ ≤
      distribution.wordMass (encode z) := by
  sorry

/-- Lemma 3.2(2); includes all preimages, not just canonical seeds. -/
theorem distribution_mass_upper (z : Instance) (hz : z.Valid)
    (hbad : peak (boundedAnswer z.machineCode z.steps z.input) ≤ (85 / 100 : ENNReal)) :
    distribution.wordMass (encode z) ≤ tailBound (encode z).length := by
  sorry

/-- Valid tuples are large enough that the accepted fraction is uniformly
bounded away from zero; this constant is absorbed by domination. -/
theorem accepted_fraction_lower (z : Instance) (hz : z.Valid) :
    (99 / 100 : ENNReal) ≤ 1 - tailBound (encode z).length := by
  sorry

/-! ## 4. Membership in AvgBPP (Lemma 3.1 and Theorem 3.1) -/

/-- Execute 200*m^2 independent trials, returning an 80%-majority Boolean
answer or giving up; enumerate all coin strings instead when k >= 2^m.
Malformed/invalid tuples return false deterministically. -/
def targetProgram (a : Word × Accuracy) : Cslib.ProbComp Answer := by
  sorry

theorem targetProgram_efficient :
    Cslib.Probability.IsPPTOn schemeInputEncoding answerEncoding targetProgram := by
  sorry

/-- The exponential branch is affordable because accuracy is unary. -/
theorem exact_branch_budget (m : ℕ) (k : Accuracy) (h : 2 ^ m ≤ k.val) :
    2 ^ m ≤ k.val + 1 := by
  sorry

/-- Low peak makes an erroneous 80%-majority rare; high peak agrees with C. -/
theorem targetProgram_correct (H : Ensemble) :
    RandomizedScheme.Correct
      (fun x k => Cslib.ProbComp.eval (targetProgram (x, k))) ⟨language, H⟩ := by
  sorry

/-- Sum the pointwise small masses over at most 2^n bad instances. -/
theorem bad_instances_mass (H : Ensemble)
    (hH : ∀ z : Instance, z.Valid →
      peak (boundedAnswer z.machineCode z.steps z.input) ≤ (85 / 100 : ENNReal) →
      H.wordMass (encode z) ≤ tailBound (encode z).length) (n : ℕ) :
    H.prob n (fun w => ∃ z, encode z = w ∧ z.Valid ∧
      peak (boundedAnswer z.machineCode z.steps z.input) ≤ (85 / 100 : ENNReal)) ≤
        (2 ^ n : ENNReal) * tailBound n := by
  sorry

theorem targetProgram_useful (H : Ensemble)
    (hH : ∀ z : Instance, z.Valid →
      peak (boundedAnswer z.machineCode z.steps z.input) ≤ (85 / 100 : ENNReal) →
      H.wordMass (encode z) ≤ tailBound (encode z).length) :
    RandomizedScheme.Useful
      (fun x k => Cslib.ProbComp.eval (targetProgram (x, k))) ⟨language, H⟩ := by
  sorry

/-- Lemma 3.1. -/
theorem avgBPP_of_small_bad_mass (H : Ensemble)
    (hH : ∀ z : Instance, z.Valid →
      peak (boundedAnswer z.machineCode z.steps z.input) ≤ (85 / 100 : ENNReal) →
      H.wordMass (encode z) ≤ tailBound (encode z).length) : AvgBPP ⟨language, H⟩ := by
  sorry

noncomputable def problem : DistributionalProblem := ⟨language, distribution⟩

/-- Theorem 3.1. -/
theorem problem_avgBPP : AvgBPP problem := by
  sorry

/-! ## 5. Amplification, compact specialization, and source compilation -/

/-- Amplify both internal constants to 0.01, preserving strict polynomial time. -/
theorem amplified_witness (P : DistributionalProblem) (hP : AvgBPP P) :
    ∃ A : PolyTimeRandomizedScheme,
      (∀ k x, P.distribution.Supports x →
        wrongProb P.language x (A.run x k) < (1 / 100 : ENNReal)) ∧
      (∀ k n, P.distribution.prob n
        (fun x => (1 / 100 : ENNReal) ≤ A.run x k none) < k.bound) := by
  obtain ⟨A, hA⟩ := hP
  obtain ⟨depth, hboost⟩ := amplification_constant A P hA (1 / 100) (by norm_num)
  refine ⟨A.amplify depth, ?_, ?_⟩
  · simpa using hboost.correct
  · simpa using hboost.useful

/-- Compile an actual PPT algorithm and specialize its unary-accuracy input
using a binary constant in the code (Remark 3.2). This requires a concrete
universal-machine simulation and a polynomial-time code constructor. -/
theorem compile_algorithm (A : PolyTimeRandomizedScheme) :
    ∃ (code : Accuracy → Word) (c d sizeCoefficient : ℕ),
      Turing.MultiTapeTM.ComputableTidilyInPolyTime
        (fun a : Word × Accuracy => code a.2)
        schemeInputEncoding (Function.Embedding.refl Word) ∧
      (∀ k, 2 ^ (code k).length ≤ sizeCoefficient * (k.val + 1)) ∧
      (∀ x k, boundedAnswer (code k)
        (c * (x.length + k.val + 2) ^ d + x.length + burnIn + 1) x = A.run x k) := by
  sorry

/-- Compile the exact sampler, including its strict clock, to boundedSample.
Normalization does not change a sampler already supported on length-n words. -/
theorem compile_sampler (D : Ensemble) (hD : PSamp D) :
    ∃ (code : Word) (c d : ℕ), ∀ n,
      boundedSample code (c * (n + 1) ^ d) n = D n := by
  sorry

/-- Compilation data only: no reduction, domination, or completeness is assumed.
Binary specialization is essential: a unary k in the code would make the
inverse seed mass exponential in k. Machine simulation overhead is absorbed
in the polynomial clock; the added input length/burn-in ensures Valid. -/
structure CompiledSource (P : DistributionalProblem) where
  algorithm : PolyTimeRandomizedScheme
  code : Accuracy → Word
  machineCoefficient : ℕ
  machineDegree : ℕ
  samplerCode : Word
  samplerCoefficient : ℕ
  samplerDegree : ℕ
  codeCoefficient : ℕ
  code_efficient : Turing.MultiTapeTM.ComputableTidilyInPolyTime
    (fun a : Word × Accuracy => code a.2)
    schemeInputEncoding (Function.Embedding.refl Word)
  code_size : ∀ k, 2 ^ (code k).length ≤ codeCoefficient * (k.val + 1)
  execution : ∀ x k,
    boundedAnswer (code k)
      (machineCoefficient * (x.length + k.val + 2) ^ machineDegree +
        x.length + burnIn + 1) x = algorithm.run x k
  sampling : ∀ n,
    boundedSample samplerCode (samplerCoefficient * (n + 1) ^ samplerDegree) n =
      P.distribution n
  correct : ∀ k x, P.distribution.Supports x →
    wrongProb P.language x (algorithm.run x k) < (1 / 100 : ENNReal)
  useful : ∀ k n, P.distribution.prob n
    (fun x => (1 / 100 : ENNReal) ≤ algorithm.run x k none) < k.bound

/-- Bridge actual PPT witnesses to binary code/universal execution, with exact
semantics and uniform polynomial clocks. This includes Remark 3.2. -/
theorem compile_source (P : DistributionalProblem)
    (hP : AvgBPP P) (hD : PSamp P.distribution) : Nonempty (CompiledSource P) := by
  obtain ⟨A, hcorrect, huseful⟩ := amplified_witness P hP
  obtain ⟨code, c, d, sizeCoefficient, hefficient, hsize, hexecution⟩ := compile_algorithm A
  obtain ⟨samplerCode, sc, sd, hsampling⟩ := compile_sampler P.distribution hD
  exact ⟨⟨A, code, c, d, samplerCode, sc, sd, sizeCoefficient,
    hefficient, hsize, hexecution, hsampling, hcorrect, huseful⟩⟩

namespace CompiledSource

variable {P : DistributionalProblem}

def queryInstance (W : CompiledSource P) (x : Word) (k : Accuracy) (b : Bool) : Instance :=
  ⟨W.code k, x,
    W.machineCoefficient * (x.length + k.val + 2) ^ W.machineDegree +
      x.length + burnIn + 1,
    b, W.samplerCode, W.samplerCoefficient * (x.length + 1) ^ W.samplerDegree⟩

def query (W : CompiledSource P) (x : Word) (k : Accuracy) (b : Bool) : Word :=
  encode (W.queryInstance x k b)

theorem query_valid (W : CompiledSource P) (x : Word) (k : Accuracy) (b : Bool) :
    (W.queryInstance x k b).Valid := by
  simp only [Instance.Valid, queryInstance]
  omega

theorem query_injective (W : CompiledSource P) (k : Accuracy) (b : Bool) :
    Function.Injective (fun x => W.query x k b) := by
  intro x y h
  have hi := encode_injective h
  exact congrArg Instance.input hi

theorem query_distinct (W : CompiledSource P) (x : Word) (k : Accuracy) :
    W.query x k false ≠ W.query x k true := by
  intro h
  have hi := encode_injective h
  have := congrArg Instance.fallback hi
  simp [queryInstance] at this

theorem query_length_eq (W : CompiledSource P) (x : Word) (k : Accuracy) :
    (W.query x k false).length = (W.query x k true).length := by
  exact encodeSeed_length_congr (W.queryInstance x k false).seed
    (W.queryInstance x k true).seed rfl rfl rfl rfl rfl

/-- Actual tidy-machine certification of constructing the query, not merely
an upper bound on the resulting word's length. -/
theorem query_efficient (W : CompiledSource P) (b : Bool) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => W.query a.1 a.2 b)
      schemeInputEncoding (Function.Embedding.refl Word) := by
  sorry

theorem seedDenominator_polynomial (W : CompiledSource P) :
    ∃ c d : ℕ, ∀ x k b,
      seedDenominator (W.queryInstance x k b) ≤ c * (x.length + k.val + 2) ^ d := by
  sorry

/-! ## 6. Certified truth-table reduction and its distributional conditions -/

/-- Must be a real finite-control machine with a uniform clock for every oracle.
Its construction composes query generation, two oracle calls, and combine. -/
noncomputable def reduction (W : CompiledSource P) : PolyTimeOracleScheme := by
  sorry

/-- Exact trace proves nonadaptivity, not just a bound of two on query count. -/
theorem reduction_trace (W : CompiledSource P) (L : Language) (x : Word) (k : Accuracy) :
    W.reduction.trace L x k =
      [(W.query x k false, L (W.query x k false)),
       (W.query x k true, L (W.query x k true))] := by
  sorry

theorem reduction_run (W : CompiledSource P) (L : Language) (x : Word) (k : Accuracy) :
    W.reduction.run L x k = combine (L (W.query x k false)) (L (W.query x k true)) := by
  sorry

theorem reduction_asks_iff (W : CompiledSource P) (L : Language)
    (x : Word) (k : Accuracy) (y : Word) :
    W.reduction.Asks L x k y ↔ y = W.query x k false ∨ y = W.query x k true := by
  simp [PolyTimeOracleScheme.Asks, PolyTimeOracleScheme.queryWords, W.reduction_trace]

theorem reduction_giveUp_iff (W : CompiledSource P) (x : Word) (k : Accuracy) :
    W.reduction.run language x k = none ↔
      (1 / 4 : ENNReal) ≤ W.algorithm.run x k none := by
  rw [W.reduction_run, combine_eq_none_iff]
  have h := query_answers_differ_iff (W.queryInstance x k false) (W.query_valid x k false)
  simpa only [query, queryInstance, W.execution] using h

theorem reduction_correct (W : CompiledSource P) :
    (W.reduction.run language).Correct P := by
  intro k x hx
  by_cases hgiveUp : (1 / 4 : ENNReal) ≤ W.algorithm.run x k none
  · exact Or.inr ((W.reduction_giveUp_iff x k).mpr hgiveUp)
  · have hbit := frequentBit_eq_of_small_wrong_and_giveUp
      (W.algorithm.run x k) (P.language x)
      (by simpa only [wrongProb_eq_mass] using W.correct k x hx)
      (lt_of_not_ge hgiveUp)
    have hfalse : language (W.query x k false) = P.language x := by
      rw [query, language_encode _ (W.query_valid x k false)]
      simp only [instanceBit, queryInstance, W.execution, if_neg hgiveUp, hbit]
    have htrue : language (W.query x k true) = P.language x := by
      rw [query, language_encode _ (W.query_valid x k true)]
      simp only [instanceBit, queryInstance, W.execution, if_neg hgiveUp, hbit]
    exact Or.inl (by rw [W.reduction_run, hfalse, htrue, combine_self])

theorem reduction_useful (W : CompiledSource P) :
    (W.reduction.run language).Useful P := by
  intro k n
  apply lt_of_le_of_lt (P.distribution.prob_mono_on_support n ?_) (W.useful k n)
  intro x _ hx
  exact (by norm_num : (1 / 100 : ENNReal) ≤ 1 / 4).trans
    ((W.reduction_giveUp_iff x k).mp hx)

def exceptional (W : CompiledSource P) (k : Accuracy) (n : ℕ) : Set (FixedWord n) :=
  {x | (1 / 100 : ENNReal) ≤ W.algorithm.run x.toWord k none}

theorem exceptional_mass (W : CompiledSource P) (k : Accuracy) (n : ℕ) :
    eventProb (P.distribution n) (W.exceptional k n) < k.bound := by
  exact W.useful k n

/-- Uniform polynomial lower bound on each query's target mass, outside E.
This combines the sampler lower bound, source correctness, and compact codes. -/
theorem query_mass_lower (W : CompiledSource P) :
    ∃ c d : ℕ, ∀ k n (x : FixedWord n), x ∉ W.exceptional k n → ∀ b,
      P.distribution n x ≤
        (PolyTimeOracleScheme.dominationFactor c d n k : ENNReal) *
          distribution.wordMass (W.query x.toWord k b) := by
  sorry

/-- Injectivity prevents collisions from accumulating many source masses.
The two fallback fibers are disjoint; queries are counted at least once. -/
theorem reduction_domination (W : CompiledSource P) :
    W.reduction.Domination P problem := by
  sorry

theorem reduction_conditions (W : CompiledSource P) :
    ErrorlessReductionConditions W.reduction P problem := by
  exact ⟨⟨W.reduction_correct, W.reduction_useful⟩, W.reduction_domination⟩

/-- This is the support consequence available from the domination argument.
There is intentionally no unconditional QueriesSupported assertion here. -/
theorem queries_supported_outside_exceptional (W : CompiledSource P)
    (k : Accuracy) (n : ℕ) (x : FixedWord n)
    (hx : P.distribution n x ≠ 0) (he : x ∉ W.exceptional k n)
    (y : Word) (hy : W.reduction.Asks language x.toWord k y) :
    distribution.Supports y := by
  sorry

end CompiledSource

/-! ## 7. Final statements -/

/-- Hardness part of Theorem 3.2, using the existing uniform-clock reduction API. -/
theorem errorlesslyReducible (P : DistributionalProblem)
    (hP : AvgBPP P) (hD : PSamp P.distribution) : ErrorlesslyReducible P problem := by
  obtain ⟨W⟩ := compile_source P hP hD
  exact ⟨W.reduction, W.reduction_conditions⟩

/-- Theorem 3.2: membership, samplability, and errorless completeness. -/
theorem complete :
    WithPSamp AvgBPP problem ∧
      ∀ P : DistributionalProblem, WithPSamp AvgBPP P → ErrorlesslyReducible P problem := by
  exact ⟨⟨problem_avgBPP, distribution_psamp⟩,
    fun P hP => errorlesslyReducible P hP.1 hP.2⟩

end AverageCaseComplexity.Completeness.TwoQuery
