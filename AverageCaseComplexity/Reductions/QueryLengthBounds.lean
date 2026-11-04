module

public import AverageCaseComplexity.Reductions.QueryBounds

@[expose] public section

namespace AverageCaseComplexity

open scoped Classical

/-- Finite query-union estimate when all relevant query lengths belong to an
explicit finite set. -/
theorem badQueryEventProb_le_cover
    (T : PolyTimeOracleScheme) (source target : DistributionalProblem)
    (k : Accuracy) (n : ℕ) (E : Set (FixedWord n)) (C η : ENNReal)
    (lengths : Finset ℕ)
    (hcover : ∀ w : FixedWord n, ∀ y : Word,
      T.Asks target.language w.toWord k y → y.length ∈ lengths)
    (hdom : ∀ y, T.queryMass target.language source.distribution k n E y ≤
      C * target.distribution.wordMass y)
    (bad : Word → Prop)
    (hbad : ∀ m ∈ lengths, target.distribution.prob m bad ≤ η) :
    eventProb (source.distribution n)
      (fun w => w ∉ E ∧ ∃ y : Word,
        T.Asks target.language w.toWord k y ∧ bad y) ≤
      C * (lengths.card : ENNReal) * η := by
  let β := Σ m : {m // m ∈ lengths}, FixedWord m.val
  let query : β → Word := fun b => b.2.toWord
  have hsubset : ∀ w : FixedWord n,
      (w ∉ E ∧ ∃ y : Word,
        T.Asks target.language w.toWord k y ∧ bad y) →
      (w ∉ E ∧ ∃ b : β,
        T.Asks target.language w.toWord k (query b) ∧ bad (query b)) := by
    intro w hw
    obtain ⟨y, hy, hbadY⟩ := hw.2
    have hlen : y.length ∈ lengths := hcover w y hy
    let b : β := ⟨⟨y.length, hlen⟩, y.get⟩
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
    _ ≤ C * (lengths.card : ENNReal) * η := by
      rw [show (∑ b : β, C * target.distribution.wordMass (query b) *
          (if bad (query b) then 1 else 0)) =
          C * ∑ b : β, if bad (query b) then target.distribution.wordMass (query b) else 0 by
            simp [Finset.mul_sum]]
      have hsum :
          (∑ b : β, if bad (query b) then target.distribution.wordMass (query b) else 0) ≤
            (lengths.card : ENNReal) * η := by
        rw [show (∑ b : β, if bad (query b) then target.distribution.wordMass (query b) else 0) =
          ∑ m : {m // m ∈ lengths}, target.distribution.prob m.val bad by
            simp [β, query, Ensemble.prob, eventProb, Ensemble.wordMass_toWord,
              Fintype.sum_sigma]]
        calc
          (∑ m : {m // m ∈ lengths}, target.distribution.prob m.val bad) ≤
              ∑ _m : {m // m ∈ lengths}, η := by
                apply Finset.sum_le_sum
                intro m hm
                exact hbad m.val m.property
          _ = (lengths.card : ENNReal) * η := by
                simp [nsmul_eq_mul]
      calc
        C * (∑ b : β, if bad (query b) then target.distribution.wordMass (query b) else 0)
            ≤ C * ((lengths.card : ENNReal) * η) := by gcongr
        _ = C * (lengths.card : ENNReal) * η := by simp [mul_assoc]

end AverageCaseComplexity
