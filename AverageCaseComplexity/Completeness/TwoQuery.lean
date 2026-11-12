module

public import AverageCaseComplexity.Completeness.TailBounds
public import AverageCaseComplexity.Completeness.ThresholdBounds
public import AverageCaseComplexity.Completeness.TupleEncoding
public import AverageCaseComplexity.Completeness.LengthNormalization
public import AverageCaseComplexity.Completeness.CompactCode
public import AverageCaseComplexity.Completeness.VoteRuntime
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

def Instance.Valid (z : Instance) : Prop := z.input.length + burnIn < z.steps

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
  · simpa only [instanceBit, h, ite_true] using (show (false ≠ true ↔ True) by simp)
  · simp only [instanceBit, h, ite_false, ne_eq, not_true_eq_false]

/-! ## 3. Algorithm 3.1 and the mass estimates (Lemma 3.2) -/

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
  rw [sampler_eval] at hw
  change w ∈ (samplerLaw n).support at hw
  obtain ⟨v, hv, hw⟩ := PMF.mem_support_bind_iff _ _ _ |>.mp hw
  have hvlength : v.length = n := by
    obtain ⟨x, _, rfl⟩ := PMF.mem_support_map_iff _ _ _ |>.mp hv
    exact FixedWord.length_toWord x
  cases hz : decodeSeed v with
  | none =>
      simp only [hz] at hw
      have heq : w = v := by simpa using hw
      simpa only [heq] using hvlength
  | some z =>
      simp only [hz] at hw
      obtain ⟨x, _, hw⟩ := PMF.mem_support_bind_iff _ _ _ |>.mp hw
      obtain ⟨accept, _, rfl⟩ := PMF.mem_support_map_iff _ _ _ |>.mp hw
      have hlength : (encodeSeed z).length = n := by
        rw [decodeSeed_encodeSeed_eq v z hz]
        exact hvlength
      cases accept
      · simp
      · change (encode ⟨z.machineCode, x.toWord, z.clockBits.length,
          z.fallback, z.samplerCode, z.samplerClockBits.length⟩).length = n
        rw [← hlength]
        apply encodeSeed_length_congr <;> simp [Instance.seed]

theorem sampler_efficient :
    Cslib.Probability.IsPPTOn unaryEncoding (Function.Embedding.refl Word) sampler := by
  sorry

/-- Normalize the executable sampler's output into a length-indexed PMF.
The fixed-length theorem shows this does not change its output law. -/
noncomputable def distribution : Ensemble :=
  fun n => fixedLengthLaw n (Cslib.ProbComp.eval (sampler n))

theorem distribution_wordDistribution (n : ℕ) :
    distribution.wordDistribution n = Cslib.ProbComp.eval (sampler n) := by
  exact fixedLengthLaw_map_toWord n _ (sampler_output_length n)

theorem distribution_psamp : PSamp distribution := by
  refine ⟨sampler, sampler_efficient, ?_⟩
  intro n
  exact (distribution_wordDistribution n).symm

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
  apply accepted_fraction_of_large
  have hpayload := payload_length_le_encode_length z
  have hvalid := hz
  simp only [Instance.Valid, burnIn] at hvalid
  omega

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
  omega

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
  classical
  unfold Ensemble.prob eventProb
  calc
    _ ≤ ∑ _x : FixedWord n, tailBound n := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs with hx
      · obtain ⟨z, hz, hvalid, hpeak⟩ := hx
        have hlength : (encode z).length = n := by rw [hz]; simp
        have hmass := hH z hvalid hpeak
        rw [hlength, hz, H.wordMass_toWord] at hmass
        exact hmass
      · exact bot_le
    _ = _ := by simp [nsmul_eq_mul]

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
  exact ⟨⟨targetProgram, targetProgram_efficient⟩,
    targetProgram_correct H, targetProgram_useful H hH⟩

noncomputable def problem : DistributionalProblem := ⟨language, distribution⟩

/-- Theorem 3.1. -/
theorem problem_avgBPP : AvgBPP problem := by
  exact avgBPP_of_small_bad_mass distribution distribution_mass_upper

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
  open Turing.MultiTapeTM in
    have hword := schemeInput_word_efficient
    have hindex := schemeInput_index_efficient
    have hlength : ComputableTidilyInPolyTime
        (fun a : Word × Accuracy => a.1.length) schemeInputEncoding encUnary :=
      ((ComputableTidilyInPolyTime.encoding_length encBits).comp hword).of_enc_eq
        (fun _ => rfl)
    have hclock : ComputableTidilyInPolyTime
        (fun a : Word × Accuracy => W.machineCoefficient *
          (a.1.length + a.2.val + 2) ^ W.machineDegree + a.1.length + burnIn + 1)
        schemeInputEncoding encUnary := by fun_prop
    have hsamplerClock : ComputableTidilyInPolyTime
        (fun a : Word × Accuracy => W.samplerCoefficient *
          (a.1.length + 1) ^ W.samplerDegree) schemeInputEncoding encUnary := by fun_prop
    change ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => encodeSeed (W.queryInstance a.1 a.2 b).seed)
      schemeInputEncoding encBits
    refine encodeSeed_efficient_with (seed := fun a : Word × Accuracy =>
      (W.queryInstance a.1 a.2 b).seed) ?_ ?_ ?_ ?_ ?_ ?_
    · exact W.code_efficient
    · exact hword
    · exact (ComputableTidilyInPolyTime.bitsReplicate true).comp hclock
    · exact ComputableTidilyInPolyTime.const b
    · exact ComputableTidilyInPolyTime.const W.samplerCode
    · exact (ComputableTidilyInPolyTime.bitsReplicate true).comp hsamplerClock

theorem seedDenominator_polynomial (W : CompiledSource P) :
    ∃ c d : ℕ, ∀ x k b,
      seedDenominator (W.queryInstance x k b) ≤ c * (x.length + k.val + 2) ^ d := by
  obtain ⟨c, d, hlength⟩ := (W.query_efficient false).polyBounded_length
  refine ⟨2 ^ 20 * (c + 1) ^ 10 * W.codeCoefficient * 2 ^ W.samplerCode.length,
    d * 10 + 1, ?_⟩
  intro x k b
  let s := x.length + k.val + 2
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hpow : 1 ≤ s ^ d := Nat.one_le_pow d s (by omega)
  have hlen : (W.query x k b).length + 1 ≤ (c + 1) * s ^ d := by
    have h := hlength (x, k)
    have h' : (W.query x k false).length ≤ c * s ^ d := by
      simpa [schemeInputEncoding, s, Nat.add_assoc] using h
    have heq : (W.query x k b).length = (W.query x k false).length := by
      cases b
      · rfl
      · exact (W.query_length_eq x k).symm
    rw [heq, Nat.add_one_mul]
    omega
  have hcode : 2 ^ ((W.code k).length + W.samplerCode.length) ≤
      W.codeCoefficient * s * 2 ^ W.samplerCode.length := by
    rw [Nat.pow_add]
    apply Nat.mul_le_mul_right
    exact (W.code_size k).trans (Nat.mul_le_mul_left _ (by dsimp [s]; omega))
  change 2 ^ 20 * ((W.query x k b).length + 1) ^ 10 *
      2 ^ ((W.code k).length + W.samplerCode.length) ≤ _
  calc
    _ ≤ 2 ^ 20 * ((c + 1) * s ^ d) ^ 10 *
        (W.codeCoefficient * s * 2 ^ W.samplerCode.length) := by gcongr
    _ = _ := by
      simp only [Nat.mul_pow, ← Nat.pow_mul, Nat.pow_add, Nat.pow_one]
      ring

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
      simp only [instanceBit, queryInstance, W.execution, ite_eq_right hgiveUp, hbit]
    have htrue : language (W.query x k true) = P.language x := by
      rw [query, language_encode _ (W.query_valid x k true)]
      simp only [instanceBit, queryInstance, W.execution, ite_eq_right hgiveUp, hbit]
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
  classical
  obtain ⟨c, d, hdenominator⟩ := W.seedDenominator_polynomial
  refine ⟨2 * c, d, ?_⟩
  intro k n x he b
  by_cases hzero : P.distribution n x = 0
  · simp [hzero]
  have hsupported : P.distribution.Supports x.toWord := ⟨n, x, rfl, hzero⟩
  have hwrong := W.correct k x.toWord hsupported
  rw [wrongProb_eq_mass] at hwrong
  have hgiveUp : W.algorithm.run x.toWord k none < (1 / 100 : ENNReal) :=
    lt_of_not_ge he
  have hpeak := peak_gt_of_small_wrong_and_giveUp
    (W.algorithm.run x.toWord k) (P.language x.toWord) hwrong hgiveUp
  have hgood : (95 / 100 : ENNReal) ≤
      peak (boundedAnswer (W.queryInstance x.toWord k b).machineCode
        (W.queryInstance x.toWord k b).steps (W.queryInstance x.toWord k b).input) := by
    simp only [queryInstance, W.execution]
    have hconst : (95 / 100 : ENNReal) ≤ 98 / 100 := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num
    exact hconst.trans hpeak.le
  have hlower := distribution_mass_lower (W.queryInstance x.toWord k b)
    (W.query_valid x.toWord k b) hgood
  have hsample :
      (boundedSample (W.queryInstance x.toWord k b).samplerCode
        (W.queryInstance x.toWord k b).samplerSteps
        (W.queryInstance x.toWord k b).input.length).map FixedWord.toWord
        (W.queryInstance x.toWord k b).input = P.distribution n x := by
    change ((boundedSample W.samplerCode
      (W.samplerCoefficient * (x.toWord.length + 1) ^ W.samplerDegree)
      x.toWord.length).map FixedWord.toWord) x.toWord = _
    rw [W.sampling]
    have hmap (y : Word) : ((P.distribution y.length).map FixedWord.toWord) y =
        P.distribution.wordMass y := by
      simp only [Ensemble.wordMass, Ensemble.prob, eventProb, PMF.map_apply, tsum_fintype]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : y = a.toWord
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    rw [hmap, P.distribution.wordMass_toWord]
  rw [hsample] at hlower
  let den := seedDenominator (W.queryInstance x.toWord k b)
  have hdenpos : 0 < den := by
    dsimp [den, seedDenominator]
    positivity
  have hdenzero : (den : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hdenpos)
  have hdenfinite : (den : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have haccept : (1 / 2 : ENNReal) ≤
      1 - tailBound (encode (W.queryInstance x.toWord k b)).length :=
    (by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num : (1 / 2 : ENNReal) ≤ 99 / 100).trans
      (accepted_fraction_lower _ (W.query_valid x.toWord k b))
  have hsmall : (1 / 2 : ENNReal) * P.distribution n x * (den : ENNReal)⁻¹ ≤
      distribution.wordMass (W.query x.toWord k b) := by
    apply le_trans _ hlower
    gcongr
  have hcancel : (2 * (den : ENNReal)) *
      ((1 / 2 : ENNReal) * P.distribution n x * (den : ENNReal)⁻¹) = P.distribution n x := by
    calc
      _ = ((2 : ENNReal) * (1 / 2)) *
          ((den : ENNReal) * (den : ENNReal)⁻¹) * P.distribution n x := by ring
      _ = _ := by
        rw [ENNReal.mul_inv_cancel hdenzero hdenfinite]
        simp only [one_div, mul_one]
        rw [ENNReal.mul_inv_cancel (by norm_num : (2 : ENNReal) ≠ 0) (by finiteness), one_mul]
  calc
    P.distribution n x = (2 * (den : ENNReal)) *
        ((1 / 2 : ENNReal) * P.distribution n x * (den : ENNReal)⁻¹) := hcancel.symm
    _ ≤ (2 * (den : ENNReal)) * distribution.wordMass (W.query x.toWord k b) := by gcongr
    _ ≤ _ := by
      have hd := hdenominator x.toWord k b
      simp only [FixedWord.length_toWord] at hd
      have hd' : (den : ENNReal) ≤ (c * (n + k.val + 2) ^ d : ℕ) := by exact_mod_cast hd
      simp only [PolyTimeOracleScheme.dominationFactor, Nat.cast_mul, Nat.cast_ofNat]
      calc
        _ ≤ (2 * (c * (n + k.val + 2) ^ d : ℕ)) *
            distribution.wordMass (W.query x.toWord k b) := by gcongr
        _ = _ := by simp only [Nat.cast_mul]; ring

/-- Injectivity prevents collisions from accumulating many source masses.
The two fallback fibers are disjoint; queries are counted at least once. -/
theorem reduction_domination (W : CompiledSource P) :
    W.reduction.Domination P problem := by
  classical
  obtain ⟨c, d, hmass⟩ := W.query_mass_lower
  refine ⟨c, d, fun k n => ⟨W.exceptional k n, (W.exceptional_mass k n).le, ?_⟩⟩
  intro y
  by_cases hex : ∃ x : FixedWord n,
      x ∉ W.exceptional k n ∧ W.reduction.Asks language x.toWord k y
  · obtain ⟨x, he, ha⟩ := hex
    have hunique (z : FixedWord n) (hz : W.reduction.Asks language z.toWord k y) : z = x := by
      have hinput : z.toWord = x.toWord := by
        rcases (W.reduction_asks_iff language z.toWord k y).mp hz with hz | hz <;>
          rcases (W.reduction_asks_iff language x.toWord k y).mp ha with hx | hx
        all_goals exact congrArg Instance.input (encode_injective (hz.symm.trans hx))
      exact List.ofFn_injective hinput
    have hquery : W.reduction.queryMass language P.distribution k n (W.exceptional k n) y =
        P.distribution n x := by
      unfold PolyTimeOracleScheme.queryMass eventProb
      rw [Finset.sum_eq_single x]
      · simp only [he, ha, not_false_eq_true, and_self, ite_true]
      · intro z _ hzx
        have hn : ¬ (z ∉ W.exceptional k n ∧ W.reduction.Asks language z.toWord k y) := by
          intro hz
          exact hzx (hunique z hz.2)
        rw [ite_eq_right hn]
      · simp
    change W.reduction.queryMass language P.distribution k n (W.exceptional k n) y ≤ _
    rw [hquery]
    rcases (W.reduction_asks_iff language x.toWord k y).mp ha with hy | hy
    · simpa only [hy, problem] using hmass k n x he false
    · simpa only [hy, problem] using hmass k n x he true
  · have hnone (x : FixedWord n) :
        ¬ (x ∉ W.exceptional k n ∧ W.reduction.Asks language x.toWord k y) := by
      intro hx
      exact hex ⟨x, hx⟩
    change W.reduction.queryMass language P.distribution k n (W.exceptional k n) y ≤ _
    simp only [PolyTimeOracleScheme.queryMass, eventProb, hnone, ite_false, Finset.sum_const_zero]
    exact bot_le

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
  obtain ⟨c, d, hmass⟩ := W.query_mass_lower
  apply (distribution.wordMass_ne_zero_iff y).mp
  intro hzero
  rcases (W.reduction_asks_iff language x.toWord k y).mp hy with hy | hy
  · have h := hmass k n x he false
    rw [← hy, hzero, mul_zero] at h
    exact hx (le_antisymm h bot_le)
  · have h := hmass k n x he true
    rw [← hy, hzero, mul_zero] at h
    exact hx (le_antisymm h bot_le)

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
