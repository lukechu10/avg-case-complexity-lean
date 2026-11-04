module

public import AverageCaseComplexity.Reductions.Definitions

@[expose] public section

namespace AverageCaseComplexity

open scoped Classical

/-- Finite union bound for event probabilities, indexed by a finite type. -/
theorem eventProb_exists_le_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (P : β → α → Prop) :
    eventProb p (fun x => ∃ b, P b x) ≤ ∑ b, eventProb p (P b) := by
  classical
  unfold eventProb
  rw [← Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : ∃ b, P b x
  · obtain ⟨b, hb⟩ := he
    have hb' : b ∈ (Finset.univ : Finset β) := Finset.mem_univ b
    have hsingle := Finset.single_le_sum
      (f := fun c => if P c x then p x else 0)
      (fun c hc => by split_ifs <;> positivity) hb'
    have he' : ∃ b, P b x := ⟨b, hb⟩
    simpa [he', hb] using hsingle
  · simp [he]

/-- The probability of a bad-query event is bounded by the sum of the
per-query source masses, for any finite list of candidate queries. -/
theorem queryEventProb_le_sum_queryMass
    (T : PolyTimeOracleScheme) (source target : DistributionalProblem)
    (k : Accuracy) (n : ℕ) (E : Set (FixedWord n)) (β : Type*) [Fintype β]
    (query : β → Word) (bad : Word → Prop) :
    eventProb (source.distribution n)
      (fun w => w ∉ E ∧ ∃ b, T.Asks target.language w.toWord k (query b) ∧ bad (query b)) ≤
      ∑ b, if bad (query b) then
        T.queryMass target.language source.distribution k n E (query b) else 0 := by
  calc
    _ ≤ ∑ b, eventProb (source.distribution n)
        (fun w => w ∉ E ∧ T.Asks target.language w.toWord k (query b) ∧ bad (query b)) := by
      have h := eventProb_exists_le_sum (source.distribution n)
        (fun b w => w ∉ E ∧ T.Asks target.language w.toWord k (query b) ∧ bad (query b))
      simpa only [exists_and_left, and_assoc] using h
    _ ≤ ∑ b, if bad (query b) then
        T.queryMass target.language source.distribution k n E (query b) else 0 := by
      apply Finset.sum_le_sum
      intro b hb
      by_cases hbad : bad (query b)
      · simp [hbad, PolyTimeOracleScheme.queryMass]
      · simp [hbad]

/-- Event probabilities are monotone under pointwise event implication. -/
theorem eventProb_mono {α : Type*} [Fintype α] (p : PMF α)
    {P R : α → Prop} (h : ∀ x, P x → R x) :
    eventProb p P ≤ eventProb p R := by
  classical
  unfold eventProb
  apply Finset.sum_le_sum
  intro x hx
  by_cases hp : P x
  · have hr := h x hp
    simp [hp, hr]
  · simp [hp]

/-- Lemma 2.2's finite query-union estimate, assuming per-query domination and
an error-probability bound through the polynomial query-length cutoff. -/
theorem badQueryEventProb_le
    (T : PolyTimeOracleScheme) (source target : DistributionalProblem)
    (k : Accuracy) (n : ℕ) (E : Set (FixedWord n)) (C η : ENNReal)
    (hdom : ∀ y, T.queryMass target.language source.distribution k n E y ≤
      C * target.distribution.wordMass y)
    (bad : Word → Prop)
    (hbad : ∀ m, m ≤ T.coefficient * (n + k.val + 2) ^ T.degree →
      target.distribution.prob m bad ≤ η) :
    eventProb (source.distribution n)
      (fun w => w ∉ E ∧ ∃ y : Word,
        T.Asks target.language w.toWord k y ∧ bad y) ≤
      C * (T.coefficient * (n + k.val + 2) ^ T.degree + 1 : ℕ) * η := by
  let Q : ℕ := T.coefficient * (n + k.val + 2) ^ T.degree
  let β := Σ m : Fin (Q + 1), FixedWord m.val
  let query : β → Word := fun b => b.2.toWord
  have hsubset : ∀ w : FixedWord n,
      (w ∉ E ∧ ∃ y : Word,
        T.Asks target.language w.toWord k y ∧ bad y) →
      (w ∉ E ∧ ∃ b : β,
        T.Asks target.language w.toWord k (query b) ∧ bad (query b)) := by
    intro w hw
    obtain ⟨y, hy, hbadY⟩ := hw.2
    have hlen := T.query_length_le target.language w.toWord k y hy
    rw [T.clock_eq] at hlen
    have hlen' : y.length ≤ Q := by simpa [Q] using hlen
    let b : β := ⟨⟨y.length, Nat.lt_succ_of_le hlen'⟩, y.get⟩
    have hquery : query b = y := by
      simp [query, b, FixedWord.toWord, List.ofFn_get]
    refine ⟨hw.1, ⟨b, ?_, ?_⟩⟩
    · simpa [hquery] using hy
    · simpa [hquery] using hbadY
  have hunion := queryEventProb_le_sum_queryMass T source target k n E
    β query bad
  have hprob_le := eventProb_mono (source.distribution n) hsubset
  calc
    eventProb (source.distribution n)
        (fun w => w ∉ E ∧ ∃ y : Word,
          T.Asks target.language w.toWord k y ∧ bad y)
      ≤ ∑ b : β, if bad (query b) then
          T.queryMass target.language source.distribution k n E (query b) else 0 :=
        hprob_le.trans hunion
    _ ≤ ∑ b : β, C * target.distribution.wordMass (query b) *
          (if bad (query b) then 1 else 0) := by
      apply Finset.sum_le_sum
      intro b hb
      by_cases hby : bad (query b)
      · simpa [hby] using hdom (query b)
      · simp [hby]
    _ ≤ C * (Q + 1 : ℕ) * η := by
      rw [show (∑ b : β, C * target.distribution.wordMass (query b) *
          (if bad (query b) then 1 else 0)) =
          C * ∑ b : β, if bad (query b) then target.distribution.wordMass (query b) else 0 by
            simp [Finset.mul_sum]]
      have hsum :
          (∑ b : β, if bad (query b) then target.distribution.wordMass (query b) else 0) ≤
            (Q + 1 : ℕ) * η := by
        rw [show (∑ b : β, if bad (query b) then target.distribution.wordMass (query b) else 0) =
          ∑ m : Fin (Q + 1), target.distribution.prob m.val bad by
            simp [β, query, Ensemble.prob, eventProb, Ensemble.wordMass_toWord,
              Fintype.sum_sigma]]
        calc
          (∑ m : Fin (Q + 1), target.distribution.prob m.val bad) ≤
              ∑ _m : Fin (Q + 1), η := by
                apply Finset.sum_le_sum
                intro m hm
                apply hbad
                exact Nat.le_of_lt_succ m.isLt
          _ = (Q + 1 : ℕ) * η := by simp [nsmul_eq_mul]
      calc
        C * (∑ b : β, if bad (query b) then target.distribution.wordMass (query b) else 0)
            ≤ C * ((Q + 1 : ℕ) * η) := by gcongr
        _ = C * (Q + 1 : ℕ) * η := by simp [mul_assoc]

end AverageCaseComplexity
