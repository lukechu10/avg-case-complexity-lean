module

public import AverageCaseComplexity.Completeness.BoundedReplayRuntime
public import AverageCaseComplexity.Completeness.TableCompiler
public import AverageCaseComplexity.Completeness.FairReplay
public import AverageCaseComplexity.Completeness.TailBounds
public import AverageCaseComplexity.Completeness.ThresholdBounds
public import AverageCaseComplexity.Completeness.TupleEncoding
public import AverageCaseComplexity.Completeness.LengthNormalization
public import AverageCaseComplexity.Completeness.CompactCode
public import AverageCaseComplexity.Completeness.VoteRuntime
public import AverageCaseComplexity.Completeness.TupleDecodingRuntime
public import AverageCaseComplexity.Completeness.ExactVoteRuntime
public import AverageCaseComplexity.Completeness.SeedMass
public import AverageCaseComplexity.Reductions.Closure
public import AverageCaseComplexity.Reductions.TwoQueryMachine
public import AverageCaseComplexity.Reductions.StateReindex
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

/-- Execute a bounded fair-coin machine on one fresh tape of `steps` bits. -/
def boundedAnswerProgram (code : Word) (steps : ℕ) (x : Word) : Cslib.ProbComp Answer :=
  replayAnswer code x <$> fairTape steps

noncomputable def boundedAnswer (code : Word) (steps : ℕ) (x : Word) : PMF Answer :=
  Cslib.ProbComp.eval (boundedAnswerProgram code steps x)

theorem boundedAnswerProgram_eval (code : Word) (steps : ℕ) (x : Word) :
    Cslib.ProbComp.eval (boundedAnswerProgram code steps x) = boundedAnswer code steps x := rfl

/-- Bounded sampler execution, truncating/padding the output to exactly n bits. -/
def boundedSampleProgram (code : Word) (steps n : ℕ) : Cslib.ProbComp (FixedWord n) :=
  replaySample code n <$> fairTape steps

noncomputable def boundedSample (code : Word) (steps n : ℕ) : PMF (FixedWord n) :=
  Cslib.ProbComp.eval (boundedSampleProgram code steps n)

/-- Compute C's bit by counting the answers on all length-`steps` coin tapes. -/
def exactLanguageBit (code : Word) (steps : ℕ) (x : Word) (fallback : Bool) : Bool :=
  exactReplayBit (replayAnswer code x) steps fallback

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
    exactLanguageBit z.machineCode z.steps z.input z.fallback = instanceBit z :=
  exactReplayBit_eq _ _ _

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
    Cslib.ProbComp Bool :=
  reliabilityProgram (boundedAnswerProgram code steps x) (200 * N ^ 2)

theorem reliabilityTest_accept_lower (code : Word) (steps : ℕ) (x : Word) (N : ℕ)
    (hN : 0 < N)
    (hgood : (95 / 100 : ENNReal) ≤ peak (boundedAnswer code steps x)) :
    1 - tailBound N ≤ Cslib.ProbComp.eval (reliabilityTest code steps x N) true := by
  rw [reliabilityTest, reliabilityProgram_eval, boundedAnswerProgram_eval]
  exact reliabilityLaw_accept_lower (boundedAnswer code steps x) N hN hgood

theorem reliabilityTest_accept_upper (code : Word) (steps : ℕ) (x : Word) (N : ℕ)
    (hbad : peak (boundedAnswer code steps x) ≤ (85 / 100 : ENNReal)) :
    Cslib.ProbComp.eval (reliabilityTest code steps x N) true ≤ tailBound N := by
  rw [reliabilityTest, reliabilityProgram_eval, boundedAnswerProgram_eval]
  exact reliabilityLaw_accept_upper_all (boundedAnswer code steps x) N hbad

/-- Algorithm 3.1: uniform seed, bounded normalized sampling, reliability filter,
canonical tuple on success, all-ones on failure; unparseable seeds are unchanged. -/
def sampler (n : ℕ) : Cslib.ProbComp Word := do
  let w ← fairTape n
  match decodeSeed w with
  | none => pure w
  | some z => do
      let x ← boundedSampleProgram z.samplerCode z.samplerClockBits.length z.input.length
      let accept ← reliabilityTest z.machineCode z.clockBits.length x.toWord n
      pure <| if accept then
        encode ⟨z.machineCode, x.toWord, z.clockBits.length,
          z.fallback, z.samplerCode, z.samplerClockBits.length⟩
        else List.replicate n true

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
  have hu : Cslib.BitString.uniformList n = uniformEnsemble.wordDistribution n := by
    unfold Cslib.BitString.uniformList Ensemble.wordDistribution
    congr 1
    ext a
    simp
  rw [sampler, Cslib.ProbComp.eval_bind, eval_fairTape, hu, samplerLaw]
  congr 1
  funext w
  cases hd : decodeSeed w with
  | none => rfl
  | some z => simp [Cslib.ProbComp.eval_bind, boundedSample]

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

section SamplerRuntime
open Turing.MultiTapeTM ComputableTidilyInPolyTime Cslib Cslib.Probability

private abbrev SeedInput := ℕ × Word
private abbrev seedInputEnc := encPair encUnary encBits
private abbrev SampledInput := SeedInput × Word
private abbrev sampledInputEnc := encPair seedInputEnc encBits

private def emitSample (p : SampledInput) (b : Bool) : Word :=
  let s := seedCandidate p.1.2
  if b then encode ⟨s.machineCode, p.2, s.clockBits.length, s.fallback, s.samplerCode,
    s.samplerClockBits.length⟩ else List.replicate p.1.1 true

private theorem emitSample_efficient : ComputableTidilyInPolyTime
    (fun p : SampledInput × Bool => emitSample p.1 p.2) (encPair sampledInputEnc encBool) encBits := by
  obtain ⟨ha,_,hc,hb,hd,he⟩ := seedCandidate_fields
  have w := (fst seedInputEnc encBits).snd'
  have x := snd seedInputEnc encBits
  have n := (fst seedInputEnc encBits).fst'
  let z := fun p : SampledInput =>
    let s := seedCandidate p.1.2
    (⟨s.machineCode,p.2,s.clockBits.length,s.fallback,s.samplerCode,s.samplerClockBits.length⟩ : Instance)
  have rep (f : SampledInput → Word) (h : ComputableTidilyInPolyTime f sampledInputEnc encBits) :
      ComputableTidilyInPolyTime (fun p => List.replicate (f p).length true) sampledInputEnc encBits := by
    simpa only [Function.comp_def] using (bitsReplicate true).comp (length_bits.comp h)
  have hyes : ComputableTidilyInPolyTime (fun p => encode (z p)) sampledInputEnc encBits := by
    apply encodeSeed_efficient_with (seed := fun p => (z p).seed)
    all_goals dsimp only [z, Instance.seed]
    · exact ha.comp w
    · exact x
    · exact rep _ (hc.comp w)
    · exact hb.comp w
    · exact hd.comp w
    · exact rep _ (he.comp w)
  have hno := (bitsReplicate true).comp n
  exact (snd sampledInputEnc encBool).ite' (hyes.comp (fst sampledInputEnc encBool))
    (hno.comp (fst sampledInputEnc encBool))

attribute [local irreducible] seedCandidate decodeSeed replaySample replayAnswer fairTape

set_option maxHeartbeats 500000 in
/-- Algorithm 3.1, assembled from certified bounded replay of the sampled source
and the candidate answer machine. All intermediate machine outputs are words. -/
theorem sampler_efficient_of_replay
    (hanswer : ComputableTidilyInPolyTime (fun p : Word × Word × Word => replayAnswer p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) answerEncoding)
    (hsample : ComputableTidilyInPolyTime (fun p : Word × ℕ × Word => (replaySample p.1 p.2.1 p.2.2).toWord)
      (encPair encBits (encPair encUnary encBits)) encBits) :
    IsPPTOn unaryEncoding (Function.Embedding.refl Word) sampler := by
  obtain ⟨ha,hx,hc,_,hd,he⟩ := seedCandidate_fields
  let z (p : SeedInput) := seedCandidate p.2
  have w := snd encUnary encBits
  have len : ComputableTidilyInPolyTime (fun p : SeedInput => (z p).input.length) seedInputEnc encUnary := by simpa only [z,Function.comp_def] using length_bits.comp (hx.comp w)
  have sc : ComputableTidilyInPolyTime (fun p : SeedInput => (z p).samplerClockBits.length) seedInputEnc encUnary := by simpa only [z,Function.comp_def] using length_bits.comp (he.comp w)
  let draw (p : SeedInput) := (fun coins => (replaySample (z p).samplerCode (z p).input.length coins).toWord) <$>
    fairTape (z p).samplerClockBits.length
  have hdraw : IsPPTOn seedInputEnc encBits draw := by
    have pf := fst seedInputEnc encBits
    have hprep : ComputableTidilyInPolyTime (fun p : SeedInput × Word => ((z p.1).samplerCode, (z p.1).input.length, p.2))
        sampledInputEnc (encPair encBits (encPair encUnary encBits)) := ((hd.comp w).comp pf).prod ((len.comp pf).prod (snd seedInputEnc encBits))
    exact (fairTape_efficient.preprocess sc).map_with (f := fun p coins => (replaySample (z p).samplerCode (z p).input.length coins).toWord) (hsample.comp hprep)
  let test (p : SampledInput) := reliabilityTest (z p.1).machineCode (z p.1).clockBits.length p.2 p.1.1
  have htest : IsPPTOn sampledInputEnc encBool test := by
    have pf := fst seedInputEnc encBits
    have ps := snd seedInputEnc encBits
    have hc' := length_bits.comp ((hc.comp w).comp pf)
    apply reliabilityProgram_efficient (count := fun p : SampledInput => 200 * p.1.1 ^ 2)
    · apply (fairTape_efficient.preprocess hc').map_with
        (f := fun p coins => replayAnswer (z p.1).machineCode p.2 coins)
      have q := fst sampledInputEnc encBits
      exact hanswer.comp ((((ha.comp w).comp pf).comp q).prod ((ps.comp q).prod (snd sampledInputEnc encBits)))
    · have hn : ComputableTidilyInPolyTime (fun p : SampledInput => p.1.1) sampledInputEnc encUnary := pf.fst'
      fun_prop
  let after (p : SampledInput) := emitSample p <$> test p
  have hafter : IsPPTOn sampledInputEnc encBits after := htest.map_with (f := emitSample) emitSample_efficient
  let body (p : SeedInput) := if (decodeSeed p.2).isSome then (draw p >>= fun x => after (p,x)) else pure p.2
  have hbody : IsPPTOn seedInputEnc encBits body :=
    IsPPTOn.cond (optionIsSome (decodeSeed_efficient.comp w))
      (hdraw.bind_with (second := fun p x => after (p,x)) hafter) w.isPPTOn
  have h := fairTape_efficient.bind_with (second := fun n w => body (n,w)) hbody
  apply h.congr
  intro n
  rw [sampler, ProbComp.eval_bind, ProbComp.eval_bind]
  congr 1
  funext w
  cases hw : decodeSeed w with
  | none => simp [body, hw]
  | some s =>
    have hz : seedCandidate w = s := by rw [← decodeSeed_encodeSeed_eq w s hw, seedCandidate_encodeSeed]
    subst s
    simp [body, hw, draw, after, test, z, boundedSampleProgram]
    rfl

end SamplerRuntime

theorem sampler_efficient :
    Cslib.Probability.IsPPTOn unaryEncoding (Function.Embedding.refl Word) sampler :=
  sampler_efficient_of_replay replayAnswer_efficient replaySample_efficient

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

theorem distribution_mass_eq_samplerLaw (y : Word) :
    distribution.wordMass y = samplerLaw y.length y := by
  rw [← wordDistribution_mass distribution y, distribution_wordDistribution, sampler_eval]

/-- Lemma 3.2(1), with a coarse polynomial encoding prefactor. -/
theorem distribution_mass_lower (z : Instance) (hz : z.Valid)
    (hgood : (95 / 100 : ENNReal) ≤ peak (boundedAnswer z.machineCode z.steps z.input)) :
    (1 - tailBound (encode z).length) *
        (boundedSample z.samplerCode z.samplerSteps z.input.length).map
          FixedWord.toWord z.input * (seedDenominator z : ENNReal)⁻¹ ≤
      distribution.wordMass (encode z) := by
  classical
  let n := (encode z).length
  let sample := boundedSample z.samplerCode z.samplerSteps z.input.length
  let A := (1 - tailBound n) * (sample.map FixedWord.toWord z.input)
  let E : FixedWord n → Prop := fun w =>
    ∃ u, decodeSeed w.toWord = some u ∧
      u.machineCode = z.machineCode ∧ u.input.length = z.input.length ∧
      u.clockBits.length = z.steps ∧ u.fallback = z.fallback ∧
      u.samplerCode = z.samplerCode ∧ u.samplerClockBits.length = z.samplerSteps
  let Q : FixedWord n → PMF Word := fun w =>
    match decodeSeed w.toWord with
    | none => PMF.pure w.toWord
    | some u => (boundedSample u.samplerCode u.samplerClockBits.length u.input.length).bind
        fun x => (Cslib.ProbComp.eval
          (reliabilityTest u.machineCode u.clockBits.length x.toWord n)).map fun accept =>
            if accept then encode ⟨u.machineCode, x.toWord, u.clockBits.length,
              u.fallback, u.samplerCode, u.samplerClockBits.length⟩
            else List.replicate n true
  have hn : 0 < n := by
    have h := payload_length_le_encode_length z
    dsimp [n]
    omega
  have hones := encode_ne_ones z n
  have hA : A = eventProb sample (fun x => x.toWord = z.input) * (1 - tailBound n) := by
    dsimp only [A]
    rw [map_apply_eq_eventProb, mul_comm]
  have hQ (w : FixedWord n) (hw : E w) : A ≤ Q w (encode z) := by
    obtain ⟨u, hd, hM, hlen, ht, hb, hS, hs⟩ := hw
    dsimp only [Q]
    simp only [hd]
    rw [hS, hs, hlen, hM, ht, hb]
    rw [hA]
    refine eventProb_mul_le_bind_apply sample _ (encode z)
      (fun x => x.toWord = z.input) (1 - tailBound n) ?_
    intro x hx
    rw [hx]
    simpa [PMF.map_apply, tsum_fintype, Fintype.sum_bool, hones] using
      reliabilityTest_accept_lower z.machineCode z.steps z.input n hn hgood
  have houter : samplerLaw n = (uniformEnsemble n).bind Q := by
    rw [samplerLaw, Ensemble.wordDistribution, PMF.bind_map]
    rfl
  have hseed : (seedDenominator z : ENNReal)⁻¹ ≤ eventProb (uniformEnsemble n) E :=
    seed_fiber_mass_lower z
  rw [distribution_mass_eq_samplerLaw, houter]
  calc
    _ = (seedDenominator z : ENNReal)⁻¹ * A := by dsimp only [A, sample, n]; ring
    _ ≤ eventProb (uniformEnsemble n) E * A := by gcongr
    _ ≤ _ := eventProb_mul_le_bind_apply (uniformEnsemble n) Q (encode z) E A hQ

private theorem mass_select (p : PMF Bool) (hit miss y : Word) (hmiss : y ≠ miss) :
    (p.map (fun b => if b then hit else miss)) y = if y = hit then p true else 0 := by
  simp [PMF.map_apply, tsum_fintype, Fintype.sum_bool, hmiss]

/-- Lemma 3.2(2); includes all preimages, not just canonical seeds. -/
theorem distribution_mass_upper (z : Instance) (_hz : z.Valid)
    (hbad : peak (boundedAnswer z.machineCode z.steps z.input) ≤ (85 / 100 : ENNReal)) :
    distribution.wordMass (encode z) ≤ tailBound (encode z).length := by
  classical
  let n := (encode z).length
  have hones := encode_ne_ones z n
  rw [distribution_mass_eq_samplerLaw]
  unfold samplerLaw Ensemble.wordDistribution
  rw [PMF.bind_map]
  refine finite_bind_apply_le (uniformEnsemble n) _ (encode z) (tailBound n) ?_
  intro seed
  dsimp only [Function.comp_apply]
  cases hd : decodeSeed seed.toWord with
  | none =>
      have hne : encode z ≠ seed.toWord := by
        intro h
        rw [← h, show decodeSeed (encode z) = some z.seed from decodeSeed_encodeSeed z.seed] at hd
        cases hd
      simp [PMF.pure_apply, hne]
  | some u =>
      dsimp only
      refine finite_bind_apply_le
        (boundedSample u.samplerCode u.samplerClockBits.length u.input.length)
        _ (encode z) (tailBound n) ?_
      intro x
      let v : Instance := ⟨u.machineCode, x.toWord, u.clockBits.length,
        u.fallback, u.samplerCode, u.samplerClockBits.length⟩
      rw [mass_select _ _ _ _ hones]
      by_cases hv : encode v = encode z
      · have hi := encode_injective hv
        have hM := congrArg Instance.machineCode hi
        have ht := congrArg Instance.steps hi
        have hx := congrArg Instance.input hi
        dsimp only [v] at hM ht hx
        have hprogram : reliabilityTest u.machineCode u.clockBits.length x.toWord n =
            reliabilityTest z.machineCode z.steps z.input n := by rw [hM, ht, hx]
        dsimp only [v] at hv
        rw [if_pos hv.symm]
        dsimp only [n] at hprogram
        rw [hprogram]
        exact reliabilityTest_accept_upper _ _ _ _ hbad
      · dsimp only [v] at hv
        rw [if_neg (Ne.symm hv)]
        exact bot_le

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
def targetProgram (a : Word × Accuracy) : Cslib.ProbComp Answer := do
  match decode a.1 with
  | none => pure (some false)
  | some z =>
    if z.input.length + burnIn < z.steps then
      if z.steps < a.2.val.size then
        pure (some (exactLanguageBit z.machineCode z.steps z.input z.fallback))
      else
        majorityProgram (boundedAnswerProgram z.machineCode z.steps z.input)
          (200 * z.steps ^ 2)
    else
      pure (some false)

/-- The exact-branch test only compares the simulated clock with the length of
`k` in binary. Its machine need not produce the exponentially long unary `2^m`. -/
theorem exactBranchTest_efficient {α : Type} {input : α ↪ Word} {steps k : α → ℕ}
    (hm : Turing.MultiTapeTM.ComputableTidilyInPolyTime steps input Turing.MultiTapeTM.encUnary)
    (hk : Turing.MultiTapeTM.ComputableTidilyInPolyTime k input Turing.MultiTapeTM.encUnary) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime (fun a => decide (steps a < (k a).size))
      input Turing.MultiTapeTM.encBool := by
  open Turing.MultiTapeTM in
    have hbits : ComputableTidilyInPolyTime (fun a => (k a).bits) input encBits :=
      (ComputableTidilyInPolyTime.unary_to_binary.comp hk).of_enc_eq (fun a => by simp [encNat_apply])
    simpa only [Function.comp_apply, Nat.size_eq_bits_len] using ComputableTidilyInPolyTime.unary_lt' hm
      (ComputableTidilyInPolyTime.length_bits.comp hbits)

open Turing.MultiTapeTM in
set_option maxHeartbeats 1000000 in
theorem targetProgram_efficient_of_replay
    (hreplay : ComputableTidilyInPolyTime
      (fun p : Word × Word × Word => replayAnswer p.1 p.2.1 p.2.2)
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits))
      answerEncoding) :
    Cslib.Probability.IsPPTOn schemeInputEncoding answerEncoding targetProgram := by
  classical
  let code : Word × Accuracy → Word := fun a => (seedCandidate a.1).machineCode
  let input : Word × Accuracy → Word := fun a => (seedCandidate a.1).input
  let steps : Word × Accuracy → ℕ := fun a => (seedCandidate a.1).clockBits.length
  let fallback : Word × Accuracy → Bool := fun a => (seedCandidate a.1).fallback
  let k : Word × Accuracy → ℕ := fun a => a.2.val
  let replay : (Word × Accuracy) × Word → Answer :=
    fun p => replayAnswer (code p.1) (input p.1) p.2
  let vote : Word × Accuracy → Bool := guardedExactVote steps k fallback replay
  have hfields := seedCandidate_fields
  have hword := schemeInput_word_efficient
  have hcode : ComputableTidilyInPolyTime code schemeInputEncoding encBits := by
    exact hfields.1.comp hword
  have hinput : ComputableTidilyInPolyTime input schemeInputEncoding encBits := by
    exact hfields.2.1.comp hword
  have hclock : ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => (seedCandidate a.1).clockBits)
      schemeInputEncoding encBits := hfields.2.2.1.comp hword
  have hsteps : ComputableTidilyInPolyTime steps schemeInputEncoding encUnary := by
    exact ComputableTidilyInPolyTime.length_bits.comp hclock
  have hfallback : ComputableTidilyInPolyTime fallback schemeInputEncoding encBool :=
    hfields.2.2.2.1.comp hword
  have hk : ComputableTidilyInPolyTime k schemeInputEncoding encUnary :=
    schemeInput_index_efficient
  have htriple : ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Word =>
        (code p.1, (input p.1, p.2)))
      (encPair schemeInputEncoding encBits)
      (encPair encBits (encPair encBits encBits)) := by
    have hf := ComputableTidilyInPolyTime.fst schemeInputEncoding encBits
    have hs := ComputableTidilyInPolyTime.snd schemeInputEncoding encBits
    exact (hcode.comp hf).prod ((hinput.comp hf).prod hs)
  have hreplay' : ComputableTidilyInPolyTime replay
      (encPair schemeInputEncoding encBits) answerEncoding := by
    exact hreplay.comp htriple
  have hvote : ComputableTidilyInPolyTime vote schemeInputEncoding encBool := by
    exact guardedExactVote_efficient hsteps hk hfallback hreplay'
  have hinputLength : ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => (input a).length + burnIn)
      schemeInputEncoding encUnary := by
    fun_prop
  have hvalid : ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => decide ((input a).length + burnIn < steps a))
      schemeInputEncoding encBool :=
    ComputableTidilyInPolyTime.unary_lt' hinputLength hsteps
  have hexact : ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => decide (steps a < (k a).size))
      schemeInputEncoding encBool := by
    exact exactBranchTest_efficient hsteps hk
  have hparsed : ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => decide ((decode a.1).isSome = true))
      schemeInputEncoding encBool := by
    have hd := (decode_efficient.comp hword).optionIsSome
    exact hd.of_enc_eq (fun a => by simp)
  have hmajorityCount : ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => 200 * steps a ^ 2)
      schemeInputEncoding encUnary := by
    fun_prop
  have hmajorityTape : Cslib.Probability.IsPPTOn schemeInputEncoding encBits
      (fun a => fairTape (steps a)) := fairTape_efficient.preprocess hsteps
  have hmajorityRun : Cslib.Probability.IsPPTOn schemeInputEncoding answerEncoding
      (fun a => boundedAnswerProgram (code a) (steps a) (input a)) := by
    exact hmajorityTape.map_with (f := fun a coins =>
      replayAnswer (code a) (input a) coins) (hreplay'.of_enc_eq (fun _ => rfl))
  have hmajority := majorityProgram_efficient hmajorityRun hmajorityCount
  have hzero : Cslib.Probability.IsPPTOn schemeInputEncoding encBits
      (fun _ : Word × Accuracy => fairTape 0) :=
    fairTape_efficient.preprocess (.const 0)
  have hsomeVote : ComputableTidilyInPolyTime
      (fun a : Word × Accuracy => some (vote a)) schemeInputEncoding answerEncoding := by
    have h : ComputableTidilyInPolyTime
        (fun a : Word × Accuracy => if vote a = true then (some true : Answer)
          else some false) schemeInputEncoding answerEncoding :=
      hvote.cond (.const (some true : Answer)) (.const (some false : Answer))
    exact h.of_enc_eq (fun a => by cases vote a <;> rfl)
  have hsomeVotePair : ComputableTidilyInPolyTime
      (fun p : (Word × Accuracy) × Word => some (vote p.1))
      (encPair schemeInputEncoding encBits) answerEncoding := by
    exact (hsomeVote.comp (ComputableTidilyInPolyTime.fst schemeInputEncoding encBits)).of_enc_eq
      (fun _ => rfl)
  have hexactRun : Cslib.Probability.IsPPTOn schemeInputEncoding answerEncoding
      (fun a => pure (some (vote a))) := by
    have hmapped := hzero.map_with (f := fun a _ => some (vote a)) hsomeVotePair
    exact hmapped.congr (fun a => by simp)
  have hconstant : Cslib.Probability.IsPPTOn schemeInputEncoding answerEncoding
      (fun _ : Word × Accuracy => pure (some false)) := by
    have hconstantPair : ComputableTidilyInPolyTime
        (fun p : (Word × Accuracy) × Word => (some false : Answer))
        (encPair schemeInputEncoding encBits) answerEncoding := .const (some false)
    have hmapped := hzero.map_with (f := fun _ _ => (some false : Answer)) hconstantPair
    exact hmapped.congr (fun _ => by simp)
  let valid : Word × Accuracy → Prop := fun a =>
    (input a).length + burnIn < steps a
  let exactBranch : Word × Accuracy → Prop := fun a => steps a < (k a).size
  have hinner : Cslib.Probability.IsPPTOn schemeInputEncoding answerEncoding
      (fun a => if exactBranch a then pure (some (vote a))
        else majorityProgram (boundedAnswerProgram (code a) (steps a) (input a))
          (200 * steps a ^ 2)) := by
    exact Cslib.Probability.IsPPTOn.ite hexact hexactRun hmajority
  have hvalidBranch : Cslib.Probability.IsPPTOn schemeInputEncoding answerEncoding
      (fun a => if valid a then
        (if exactBranch a then pure (some (vote a))
        else majorityProgram (boundedAnswerProgram (code a) (steps a) (input a))
          (200 * steps a ^ 2))
        else pure (some false)) := by
    exact Cslib.Probability.IsPPTOn.ite hvalid hinner hconstant
  let parsed : Word × Accuracy → Prop := fun a => (decode a.1).isSome = true
  have hstaged : Cslib.Probability.IsPPTOn schemeInputEncoding answerEncoding
      (fun a => if parsed a then
          (if valid a then
            (if exactBranch a then pure (some (vote a))
            else majorityProgram (boundedAnswerProgram (code a) (steps a) (input a))
              (200 * steps a ^ 2))
          else pure (some false))
        else pure (some false)) := by
    exact Cslib.Probability.IsPPTOn.ite hparsed hvalidBranch hconstant
  apply hstaged.congr
  intro a
  unfold targetProgram
  split
  · rename_i hparsed
    have hsome : (decode a.1).isSome = true := by simpa [parsed] using hparsed
    rcases Option.isSome_iff_exists.mp hsome with ⟨z, hdec⟩
    have hx : encode z = a.1 := decode_sound a.1 z hdec
    have hcand : instanceCandidate a.1 = z := by
      rw [← hx]
      exact instanceCandidate_encode z
    have hcodeEq : code a = z.machineCode := by
      change (instanceCandidate a.1).machineCode = z.machineCode
      exact congrArg Instance.machineCode hcand
    have hinputEq : input a = z.input := by
      change (instanceCandidate a.1).input = z.input
      exact congrArg Instance.input hcand
    have hstepsEq : steps a = z.steps := by
      change (instanceCandidate a.1).steps = z.steps
      exact congrArg Instance.steps hcand
    have hfallbackEq : fallback a = z.fallback := by
      change (instanceCandidate a.1).fallback = z.fallback
      exact congrArg Instance.fallback hcand
    have hvote_eq (he : z.steps < a.2.val.size) :
        vote a = exactLanguageBit z.machineCode z.steps z.input z.fallback := by
      dsimp [vote]
      rw [guardedExactVote_eq_guardedReplayBit]
      simp only [hstepsEq, k, he, if_pos, hfallbackEq]
      congr 1
      funext coins
      simp [replay, hcodeEq, hinputEq]
    by_cases hv : z.input.length + burnIn < z.steps
    · by_cases he : z.steps < a.2.val.size
      · simp [hdec, valid, exactBranch, hinputEq, hstepsEq, hcodeEq, k, hv, he,
          hvote_eq he]
      · simp [hdec, valid, exactBranch, hinputEq, hstepsEq, hcodeEq, k, hv, he,
          majorityProgram_eval, boundedAnswerProgram_eval]
    · simp [hdec, valid, exactBranch, hinputEq, hstepsEq, hcodeEq, k, hv,
        majorityProgram_eval, boundedAnswerProgram_eval]
  · rename_i hparsed
    have hnone : decode a.1 = none := by
      by_contra hn
      have hs : (decode a.1).isSome = true := Option.isSome_iff_ne_none.mpr hn
      exact hparsed (by simpa [parsed] using hs)
    simp [hnone]

theorem targetProgram_efficient :
    Cslib.Probability.IsPPTOn schemeInputEncoding answerEncoding targetProgram :=
  targetProgram_efficient_of_replay replayAnswer_efficient

/-- Arithmetic bound on the exact branch's enumeration count. The full
machine-level cost of enumeration and simulation remains to be certified. -/
theorem exact_branch_budget (m : ℕ) (k : Accuracy) (h : 2 ^ m ≤ k.val) :
    2 ^ m ≤ k.val + 1 := by
  omega

/-- Low peak makes an erroneous 80%-majority rare; high peak agrees with C. -/
theorem targetProgram_correct (H : Ensemble) :
    RandomizedScheme.Correct
      (fun x k => Cslib.ProbComp.eval (targetProgram (x, k))) ⟨language, H⟩ := by
  intro k x _
  change wrongProb language x (Cslib.ProbComp.eval (targetProgram (x, k))) < (1 / 4 : ENNReal)
  rw [wrongProb_eq_mass]
  cases hd : decode x with
  | none =>
      simp [targetProgram, hd, language, PMF.pure_apply]
  | some z =>
      have hx : encode z = x := decode_sound x z hd
      rw [← hx]
      by_cases hz : z.Valid
      · change z.input.length + burnIn < z.steps at hz
        rw [language_encode z (by exact hz)]
        by_cases he : z.steps < k.val.size
        · simp [targetProgram, decode_encode, hz, he, exactLanguageBit_eq]
        · have hev : Cslib.ProbComp.eval (targetProgram (encode z, k)) =
              majorityLaw (boundedAnswer z.machineCode z.steps z.input) (200 * z.steps ^ 2) := by
            simp [targetProgram, decode_encode, hz, he, majorityProgram_eval,
              boundedAnswerProgram_eval]
          rw [hev]
          change majorityLaw (boundedAnswer z.machineCode z.steps z.input)
            (200 * z.steps ^ 2) (some (!instanceBit z)) < (1 / 4 : ENNReal)
          simpa [instanceBit, fallbackBit] using
            majorityLaw_wrong_lt_quarter (boundedAnswer z.machineCode z.steps z.input)
              z.fallback z.steps (by
                have hv := hz
                simp only [Instance.Valid, burnIn] at hv
                omega)
      · change ¬ z.input.length + burnIn < z.steps at hz
        simp [targetProgram, decode_encode, language, Instance.Valid, hz]

/-- A large conditional give-up probability can only occur on a low-peak
instance and only in the sampling branch. -/
theorem targetProgram_giveUp_bad (k : Accuracy) (x : Word)
    (hgive : (1 / 4 : ENNReal) ≤
      Cslib.ProbComp.eval (targetProgram (x, k)) none) :
    ∃ z, encode z = x ∧ z.Valid ∧
      peak (boundedAnswer z.machineCode z.steps z.input) ≤ (85 / 100 : ENNReal) ∧
      k.val < 2 ^ z.steps := by
  cases hd : decode x with
  | none =>
      simp [targetProgram, hd] at hgive
  | some z =>
      have hx : encode z = x := decode_sound x z hd
      rw [← hx] at hgive
      by_cases hz : z.Valid
      · change z.input.length + burnIn < z.steps at hz
        by_cases he : z.steps < k.val.size
        · simp [targetProgram, decode_encode, hz, he] at hgive
        · have hev : Cslib.ProbComp.eval (targetProgram (encode z, k)) none =
              majorityLaw (boundedAnswer z.machineCode z.steps z.input)
                (200 * z.steps ^ 2) none := by
            simp [targetProgram, decode_encode, hz, he, majorityProgram_eval,
              boundedAnswerProgram_eval]
          rw [hev] at hgive
          by_cases hpeak : peak (boundedAnswer z.machineCode z.steps z.input) ≤
              (85 / 100 : ENNReal)
          · exact ⟨z, hx, hz, hpeak, lt_of_not_ge (he ∘ Nat.lt_size.mpr)⟩
          · have hgood : (85 / 100 : ENNReal) ≤
                peak (boundedAnswer z.machineCode z.steps z.input) := le_of_not_ge hpeak
            have hlarge : 2 ≤ z.steps := by
              simp only [Instance.Valid, burnIn] at hz
              omega
            have hN : 0 < 200 * z.steps ^ 2 := by positivity
            have htail := majorityLaw_giveUp (boundedAnswer z.machineCode z.steps z.input)
              (200 * z.steps ^ 2) hN hgood
            have hsmall : ENNReal.ofReal (Real.exp (-((z.steps : ℝ) ^ 2))) <
                (1 / 4 : ENNReal) := single_tail_lt_quarter hlarge
            have hscale : -( ((200 * z.steps ^ 2 : ℕ) : ℝ)) / 200 =
                -((z.steps : ℝ) ^ 2) := by push_cast; ring
            rw [hscale] at htail
            exact False.elim (not_le_of_gt (lt_of_le_of_lt htail hsmall) hgive)
      · change ¬ z.input.length + burnIn < z.steps at hz
        simp [targetProgram, decode_encode, language, Instance.Valid, hz] at hgive

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
  intro k n
  let E : Word → Prop := fun x =>
    (1 / 4 : ENNReal) ≤ Cslib.ProbComp.eval (targetProgram (x, k)) none
  let B : Word → Prop := fun x => ∃ z, encode z = x ∧ z.Valid ∧
    peak (boundedAnswer z.machineCode z.steps z.input) ≤ (85 / 100 : ENNReal)
  have hsub : H.prob n E ≤ H.prob n B :=
    H.prob_mono_on_length n (fun x _ hs he => by
      obtain ⟨z, henc, hz, hpeak, _⟩ := targetProgram_giveUp_bad k x he
      exact ⟨z, henc, hz, hpeak⟩)
  have hbad := bad_instances_mass H hH n
  by_cases hk : k.val < 2 ^ n
  · by_cases hn : 3 ≤ n
    · calc
        H.prob n E ≤ H.prob n B := hsub
        _ ≤ (2 ^ n : ENNReal) * tailBound n := hbad
        _ < (k.val : ENNReal)⁻¹ := by
          calc
            _ < (2 ^ n : ENNReal)⁻¹ := binary_union_tail_lt hn
            _ ≤ (k.val : ENNReal)⁻¹ := by
              apply ENNReal.inv_le_inv.mpr
              exact_mod_cast hk.le
        _ = k.bound := by simp [Accuracy.bound]
    · have hzero : H.prob n E = 0 := by
        apply le_antisymm
        · have hle : H.prob n E ≤ H.prob n (fun _ : Word => False) :=
            H.prob_mono_on_length n (E := E) (F := fun _ : Word => False)
              (fun x hxlen hs he => False.elim (by
            obtain ⟨z, henc, hz, _, _⟩ := targetProgram_giveUp_bad k x he
            have hstep : z.steps ≤ n := by
              calc
                z.steps ≤ (encode z).length := by
                  have hp := payload_length_le_encode_length z
                  omega
                _ = n := by rw [henc]; exact hxlen
            have hv := hz
            simp only [Instance.Valid, burnIn] at hv
            omega))
          simpa [E, Ensemble.prob] using hle
        · exact bot_le
      rw [hzero]
      exact Accuracy.bound_pos k
  · have hzero : H.prob n E = 0 := by
      apply le_antisymm
      · have hle : H.prob n E ≤ H.prob n (fun _ : Word => False) :=
          H.prob_mono_on_length n (E := E) (F := fun _ : Word => False)
            (fun x hxlen hs he => False.elim (by
          obtain ⟨z, henc, _, _, hclock⟩ := targetProgram_giveUp_bad k x he
          have hstep : z.steps ≤ n := by
            calc
              z.steps ≤ (encode z).length := by
                have hp := payload_length_le_encode_length z
                omega
              _ = n := by rw [henc]; exact hxlen
          have hp : 2 ^ z.steps ≤ 2 ^ n := by gcongr
          have hk' : 2 ^ n ≤ k.val := Nat.le_of_not_gt hk
          omega))
        simpa [E, Ensemble.prob] using hle
      · exact bot_le
    rw [hzero]
    exact Accuracy.bound_pos k

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
  obtain ⟨header,c,d,hlaw⟩ := specialize_clocked_source rawCompiler_correct A
  exact ⟨specializeCode header, c, d, _, specializeCode_efficient header,
    specializeCode_size header, hlaw⟩

/-- Compile the exact sampler, including its strict clock, to boundedSample.
Normalization does not change a sampler already supported on length-n words. -/
theorem compile_sampler (D : Ensemble) (hD : PSamp D) :
    ∃ (code : Word) (c d : ℕ), ∀ n,
      boundedSample code (c * (n + 1) ^ d) n = D n := by
  exact replay_clocked_sampler rawCompiler_correct D hD

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

/-- Internal packaged witness: retain the exact execution theorem alongside the
finite-control machine so the reduction's trace and output use that same machine. -/
structure ReductionData (W : CompiledSource P) where
  workTapes : ℕ
  stateCount : ℕ
  machine : OracleMachine workTapes stateCount
  coefficient : ℕ
  degree : ℕ
  run_exact : ∀ (a : Word × Accuracy) (L : Language),
    _root_.AverageCaseComplexity.OracleMachine.run machine L
      (coefficient * ((schemeInputEncoding a).length + 1) ^ degree)
      (schemeInputEncoding a) =
        (_root_.AverageCaseComplexity.OracleMachine.wordConfig (schemeInputEncoding a) none [] [L (W.query a.1 a.2 true)]
          (answerEncoding (combine (L (W.query a.1 a.2 false))
            (L (W.query a.1 a.2 true)))),
          [(W.query a.1 a.2 false, L (W.query a.1 a.2 false)),
           (W.query a.1 a.2 true, L (W.query a.1 a.2 true))])

noncomputable def reductionData (W : CompiledSource P) : ReductionData W := by
  classical
  choose tapes State hfinite M c d hrun using
    (_root_.AverageCaseComplexity.OracleMachine.exists_twoQuery_machine schemeInputEncoding
      (fun a : Word × Accuracy => W.query a.1 a.2 false)
      (fun a : Word × Accuracy => W.query a.1 a.2 true)
      (W.query_efficient false) (W.query_efficient true))
  letI : Finite State := hfinite
  letI : Fintype State := Fintype.ofFinite State
  let e : State ≃ Fin (Fintype.card State) := Fintype.equivFin State
  refine ⟨tapes, Fintype.card State, _root_.AverageCaseComplexity.OracleMachine.reindex M e, c, d, ?_⟩
  intro a L
  rw [_root_.AverageCaseComplexity.OracleMachine.run_reindex]
  rw [hrun a L]
  rfl

/-- Must be a real finite-control machine with a uniform clock for every oracle.
Its construction composes query generation, two oracle calls, and combine. -/
noncomputable def reduction (W : CompiledSource P) : PolyTimeOracleScheme := by
  let D := reductionData W
  refine ⟨D.workTapes, D.stateCount, D.machine, D.coefficient, D.degree, ?_, ?_⟩
  · intro L a
    change (OracleMachine.run D.machine L
      (D.coefficient * ((schemeInputEncoding a).length + 1) ^ D.degree)
      (schemeInputEncoding a)).1.tapes.state = none
    rw [D.run_exact]
    rfl
  · intro L a
    refine ⟨combine (L (W.query a.1 a.2 false)) (L (W.query a.1 a.2 true)), ?_⟩
    change (OracleMachine.run D.machine L
      (D.coefficient * ((schemeInputEncoding a).length + 1) ^ D.degree)
      (schemeInputEncoding a)).1.tapes.output = _
    rw [D.run_exact]
    rfl

/-- Exact trace proves nonadaptivity, not just a bound of two on query count. -/
theorem reduction_trace (W : CompiledSource P) (L : Language) (x : Word) (k : Accuracy) :
    W.reduction.trace L x k =
      [(W.query x k false, L (W.query x k false)),
       (W.query x k true, L (W.query x k true))] := by
  change (_root_.AverageCaseComplexity.OracleMachine.run (reductionData W).machine L
    ((reductionData W).coefficient * ((schemeInputEncoding (x, k)).length + 1) ^
      (reductionData W).degree)
    (schemeInputEncoding (x, k))).2 = _
  rw [(reductionData W).run_exact (x, k) L]

theorem reduction_run (W : CompiledSource P) (L : Language) (x : Word) (k : Accuracy) :
    W.reduction.run L x k = combine (L (W.query x k false)) (L (W.query x k true)) := by
  change decodeOracleAnswer (_root_.AverageCaseComplexity.OracleMachine.run (reductionData W).machine L
    ((reductionData W).coefficient * ((schemeInputEncoding (x, k)).length + 1) ^
      (reductionData W).degree)
    (schemeInputEncoding (x, k))).1.tapes.output = _
  rw [(reductionData W).run_exact (x, k) L]
  simp [OracleMachine.wordConfig]

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
