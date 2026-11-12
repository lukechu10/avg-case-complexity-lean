module

public import AverageCaseComplexity.Completeness.TupleEncoding
public import AverageCaseComplexity.Completeness.LengthNormalization
public import AverageCaseComplexity.Distributions

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

/-- Coarse polynomial denominator used for the mass of a seed fiber. -/
def seedDenominator (z : Instance) : ℕ :=
  2 ^ 20 * ((encode z).length + 1) ^ 10 *
    2 ^ (z.machineCode.length + z.samplerCode.length)

/-- An injective family of event members contributes the sum of its masses.
Factoring this out keeps the finite-sum proof independent of tuple encodings. -/
theorem sum_injective_le_eventProb {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF β) (f : α → β) (hf : Function.Injective f) (E : β → Prop)
    (hE : ∀ a, E (f a)) : (∑ a, p (f a)) ≤ eventProb p E := by
  classical
  let image := Finset.univ.image f
  calc
    _ = ∑ b ∈ image, p b := by
      dsimp only [image]
      rw [Finset.sum_image]
      exact fun a _ b _ h => hf h
    _ = ∑ b ∈ image, if E b then p b else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
      rw [ite_eq_left (hE a)]
    _ ≤ eventProb p E := by
      unfold eventProb
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ image)
      intro b _ _
      exact bot_le

/-- A pointwise upper bound survives averaging over a finite probability law. -/
theorem finite_bind_apply_le {α β : Type*} [Fintype α] (p : PMF α)
    (q : α → PMF β) (b : β) (C : ENNReal) (h : ∀ a, q a b ≤ C) :
    p.bind q b ≤ C := by
  rw [PMF.bind_apply, tsum_fintype]
  calc
    _ ≤ ∑ a, p a * C := by
      apply Finset.sum_le_sum
      intro a _
      gcongr
      exact h a
    _ = (∑ a, p a) * C := (Finset.sum_mul _ _ _).symm
    _ = C := by
      have hp : (∑ a, p a) = 1 := by simpa only [tsum_fintype] using p.tsum_coe
      rw [hp, one_mul]

/-- Finite map mass is the probability of the corresponding preimage event. -/
theorem map_apply_eq_eventProb {α β : Type*} [Fintype α]
    (p : PMF α) (f : α → β) (b : β) :
    p.map f b = eventProb p (fun a => f a = b) := by
  classical
  rw [PMF.map_apply, tsum_fintype, eventProb]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- Retaining only inputs in an event gives a lower bound on a finite bind. -/
theorem eventProb_mul_le_bind_apply {α β : Type*} [Fintype α] (p : PMF α)
    (q : α → PMF β) (b : β) (E : α → Prop) (C : ENNReal)
    (h : ∀ a, E a → C ≤ q a b) : eventProb p E * C ≤ p.bind q b := by
  classical
  rw [eventProb, PMF.bind_apply, tsum_fintype, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : E a
  · rw [ite_eq_left ha]
    gcongr
    exact h a ha
  · rw [ite_eq_right ha, zero_mul]
    exact bot_le

/-- The uniform seed mass of the full fiber of irrelevant input, clock, and
sampler-clock bits. The proof counts every choice of those free bits. -/
theorem seed_fiber_mass_lower (z : Instance) :
    (seedDenominator z : ENNReal)⁻¹ ≤
      eventProb (uniformEnsemble (encode z).length) (fun w =>
        ∃ u, decodeSeed w.toWord = some u ∧
          u.machineCode = z.machineCode ∧ u.input.length = z.input.length ∧
          u.clockBits.length = z.steps ∧ u.fallback = z.fallback ∧
          u.samplerCode = z.samplerCode ∧ u.samplerClockBits.length = z.samplerSteps) := by
  classical
  let N := (encode z).length
  let Src := FixedWord z.input.length × FixedWord z.steps × FixedWord z.samplerSteps
  let f : Src → FixedWord N := fun q =>
    normalizeWord N (encodeSeed ⟨z.machineCode, q.1.toWord,
      q.2.1.toWord, z.fallback, z.samplerCode, q.2.2.toWord⟩)
  have hlen (q : Src) :
      (encodeSeed ⟨z.machineCode, q.1.toWord, q.2.1.toWord,
        z.fallback, z.samplerCode, q.2.2.toWord⟩).length = N := by
    dsimp [N]
    apply encodeSeed_length_congr <;> simp [Instance.seed]
  have hround (q : Src) : (f q).toWord =
      encodeSeed ⟨z.machineCode, q.1.toWord, q.2.1.toWord,
        z.fallback, z.samplerCode, q.2.2.toWord⟩ := by
    exact normalizeWord_toWord _ (hlen q)
  have hinj : Function.Injective f := by
    intro q r h
    have heq :
        encodeSeed ⟨z.machineCode, q.1.toWord, q.2.1.toWord,
          z.fallback, z.samplerCode, q.2.2.toWord⟩ =
        encodeSeed ⟨z.machineCode, r.1.toWord, r.2.1.toWord,
          z.fallback, z.samplerCode, r.2.2.toWord⟩ := by
      calc
        _ = (f q).toWord := (hround q).symm
        _ = (f r).toWord := congrArg FixedWord.toWord h
        _ = _ := hround r
    have hseed := congrArg decodeSeed heq
    simp only [decodeSeed_encodeSeed] at hseed
    have hstruct :
        (⟨z.machineCode, q.1.toWord, q.2.1.toWord,
          z.fallback, z.samplerCode, q.2.2.toWord⟩ : Seed) =
        ⟨z.machineCode, r.1.toWord, r.2.1.toWord,
          z.fallback, z.samplerCode, r.2.2.toWord⟩ := Option.some.inj hseed
    have hinput : q.1.toWord = r.1.toWord := congrArg Seed.input hstruct
    have hclock : q.2.1.toWord = r.2.1.toWord := congrArg Seed.clockBits hstruct
    have hsampler : q.2.2.toWord = r.2.2.toWord := congrArg Seed.samplerClockBits hstruct
    have hq : q.1 = r.1 := by
      change List.ofFn q.1 = List.ofFn r.1 at hinput
      exact List.ofFn_inj.mp hinput
    have hm : q.2.1 = r.2.1 := by
      change List.ofFn q.2.1 = List.ofFn r.2.1 at hclock
      exact List.ofFn_inj.mp hclock
    have hs : q.2.2 = r.2.2 := by
      change List.ofFn q.2.2 = List.ofFn r.2.2 at hsampler
      exact List.ofFn_inj.mp hsampler
    exact Prod.ext hq (Prod.ext hm hs)
  have hfiber (q : Src) :
      ∃ u, decodeSeed (f q).toWord = some u ∧
        u.machineCode = z.machineCode ∧ u.input.length = z.input.length ∧
        u.clockBits.length = z.steps ∧ u.fallback = z.fallback ∧
        u.samplerCode = z.samplerCode ∧ u.samplerClockBits.length = z.samplerSteps := by
    refine ⟨⟨z.machineCode, q.1.toWord, q.2.1.toWord,
      z.fallback, z.samplerCode, q.2.2.toWord⟩, ?_, rfl, ?_, ?_, rfl, rfl, ?_⟩
    · rw [hround q, decodeSeed_encodeSeed]
    · simp
    · simp
    · simp
  have hprob :
      (Fintype.card Src : ENNReal) * (2 ^ N : ENNReal)⁻¹ ≤
        eventProb (uniformEnsemble N) (fun w =>
          ∃ u, decodeSeed w.toWord = some u ∧
            u.machineCode = z.machineCode ∧ u.input.length = z.input.length ∧
            u.clockBits.length = z.steps ∧ u.fallback = z.fallback ∧
            u.samplerCode = z.samplerCode ∧ u.samplerClockBits.length = z.samplerSteps) := by
    calc
      _ = ∑ q : Src, uniformEnsemble N (f q) := by
        simp only [uniformEnsemble_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := sum_injective_le_eventProb (uniformEnsemble N) f hinj _ hfiber
  have hcard : Fintype.card Src = 2 ^ (z.input.length + z.steps + z.samplerSteps) := by
    simp [Src, Fintype.card_prod, Fintype.card_bool, Nat.add_assoc, pow_add]
  rw [hcard] at hprob
  have hNbound : N ≤ z.machineCode.length + z.samplerCode.length +
      z.input.length + z.steps + z.samplerSteps + 20 + 10 * Nat.log2 (N + 1) := by
    have hformula : N = z.machineCode.length + z.input.length + z.steps + 1 +
        z.samplerCode.length + z.samplerSteps + 2 * z.machineCode.length.size +
        2 * z.input.length.size + 2 * z.steps.size +
        2 * z.samplerCode.length.size + 4 := by
      dsimp [N, encode]
      simpa [Instance.seed] using (encodeSeed_length_eq z.seed)
    have hNpos : N + 1 ≠ 0 := by omega
    have hpow : N + 1 < 2 ^ (Nat.log2 (N + 1) + 1) := by
      rw [Nat.log2_eq_log_two]
      apply (Nat.log_lt_iff_lt_pow Nat.one_lt_two hNpos).mp
      omega
    have hpayload := payload_length_le_encode_length z
    have hMlen : z.machineCode.length ≤ N := by dsimp [N]; omega
    have hxlen : z.input.length ≤ N := by dsimp [N]; omega
    have hmlen : z.steps ≤ N := by dsimp [N]; omega
    have hSlen : z.samplerCode.length ≤ N := by dsimp [N]; omega
    have hM : z.machineCode.length.size ≤ Nat.log2 (N + 1) + 1 := by
      apply Nat.size_le.mpr
      omega
    have hx : z.input.length.size ≤ Nat.log2 (N + 1) + 1 := by
      apply Nat.size_le.mpr
      omega
    have hm : z.steps.size ≤ Nat.log2 (N + 1) + 1 := by
      apply Nat.size_le.mpr
      omega
    have hS : z.samplerCode.length.size ≤ Nat.log2 (N + 1) + 1 := by
      apply Nat.size_le.mpr
      omega
    omega
  have hexp : N ≤ 20 + 10 * Nat.log2 (N + 1) +
      z.machineCode.length + z.samplerCode.length +
      z.input.length + z.steps + z.samplerSteps := by omega
  have hpowden : 2 ^ N ≤
      (2 ^ 20 * (N + 1) ^ 10 * 2 ^ (z.machineCode.length + z.samplerCode.length)) *
        2 ^ (z.input.length + z.steps + z.samplerSteps) := by
    have hbase : 2 ^ Nat.log2 (N + 1) ≤ N + 1 := Nat.log2_self_le (by omega)
    calc
      2 ^ N ≤ 2 ^ (20 + 10 * Nat.log2 (N + 1) + z.machineCode.length +
          z.samplerCode.length + z.input.length + z.steps + z.samplerSteps) :=
        Nat.pow_le_pow_right (by omega) hexp
      _ = 2 ^ 20 * (2 ^ Nat.log2 (N + 1)) ^ 10 *
          2 ^ (z.machineCode.length + z.samplerCode.length) *
          2 ^ (z.input.length + z.steps + z.samplerSteps) := by
        simp only [pow_add]
        rw [show 10 * Nat.log2 (N + 1) = Nat.log2 (N + 1) * 10 by omega, pow_mul]
        ring
      _ ≤ _ := by gcongr
  have hmassbound :
      (2 ^ (z.input.length + z.steps + z.samplerSteps) : ENNReal) *
          (2 ^ N : ENNReal)⁻¹ ≥
        (seedDenominator z : ENNReal)⁻¹ := by
    have hc : (seedDenominator z : ENNReal) *
        (2 ^ (z.input.length + z.steps + z.samplerSteps) : ENNReal) ≥
        (2 ^ N : ENNReal) := by
      exact_mod_cast hpowden
    have hpos : (2 ^ N : ENNReal) ≠ 0 := by positivity
    have hdenpos : (seedDenominator z : ENNReal) ≠ 0 := by
      unfold seedDenominator
      positivity
    apply (ENNReal.le_div_iff_mul_le (Or.inl hpos)
      (Or.inl (ENNReal.pow_ne_top (by norm_num)))).2
    calc
      (seedDenominator z : ENNReal)⁻¹ * (2 ^ N : ENNReal)
          ≤ (seedDenominator z : ENNReal)⁻¹ *
              ((seedDenominator z : ENNReal) *
                (2 ^ (z.input.length + z.steps + z.samplerSteps) : ENNReal)) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2 ^ (z.input.length + z.steps + z.samplerSteps) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hdenpos (by finiteness), one_mul]
  have hprob' :
      (2 ^ (z.input.length + z.steps + z.samplerSteps) : ENNReal) *
          (2 ^ N : ENNReal)⁻¹ ≤
        eventProb (uniformEnsemble N) (fun w =>
          ∃ u, decodeSeed w.toWord = some u ∧
            u.machineCode = z.machineCode ∧ u.input.length = z.input.length ∧
            u.clockBits.length = z.steps ∧ u.fallback = z.fallback ∧
            u.samplerCode = z.samplerCode ∧ u.samplerClockBits.length = z.samplerSteps) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hprob
  calc
    (seedDenominator z : ENNReal)⁻¹ ≤
        (2 ^ (z.input.length + z.steps + z.samplerSteps) : ENNReal) *
          (2 ^ N : ENNReal)⁻¹ := hmassbound
    _ ≤ _ := hprob'

end AverageCaseComplexity.Completeness.TwoQuery
