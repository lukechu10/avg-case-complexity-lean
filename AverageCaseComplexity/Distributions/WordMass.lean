module

public import AverageCaseComplexity.Distributions

@[expose] public section

namespace AverageCaseComplexity

/-- The paper's `D(y)`: the mass of `y` in the ensemble component at its own length.
This is not a probability distribution over words of all lengths. -/
noncomputable def Ensemble.wordMass (D : Ensemble) (y : Word) : ENNReal :=
  D.prob y.length (fun x => x = y)

@[simp] theorem Ensemble.wordMass_toWord (D : Ensemble) {n : ℕ} (w : FixedWord n) :
    D.wordMass w.toWord = D n w := by
  classical
  unfold Ensemble.wordMass
  rw [FixedWord.length_toWord]
  simp [Ensemble.prob, eventProb, FixedWord.toWord, List.ofFn_inj]

/-- Every ordinary word has the mass supplied by its own length component. -/
theorem Ensemble.wordMass_eq (D : Ensemble) (y : Word) :
    D.wordMass y = D y.length y.get := by
  have h := D.wordMass_toWord y.get
  simpa only [FixedWord.toWord, List.ofFn_get] using h

/-- A word has positive ensemble mass exactly when it is supported. -/
theorem Ensemble.wordMass_ne_zero_iff (D : Ensemble) (y : Word) :
    D.wordMass y ≠ 0 ↔ D.Supports y := by
  constructor
  · intro h
    exact ⟨y.length, y.get, List.ofFn_get y, by simpa only [D.wordMass_eq] using h⟩
  · rintro ⟨n, w, rfl, hw⟩
    simpa using hw

@[simp] theorem Ensemble.wordMass_ne_top (D : Ensemble) (y : Word) :
    D.wordMass y ≠ ⊤ := by
  rw [D.wordMass_eq]
  exact (D y.length).apply_ne_top _

end AverageCaseComplexity
