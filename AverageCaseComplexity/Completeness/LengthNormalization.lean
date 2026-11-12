module

public import AverageCaseComplexity.Sampling
public import AverageCaseComplexity.Distributions.WordMass

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

/-- Truncate or pad an arbitrary output word to exactly the requested length.
Padding uses false. This definition is executable; a machine runtime certificate
for its use in the universal sampler is a separate obligation. -/
def normalizeWord (n : ℕ) (w : Word) : FixedWord n :=
  fun i => w[i.val]?.getD false

theorem normalizeWord_toWord {n : ℕ} (w : Word) (hw : w.length = n) :
    (normalizeWord n w).toWord = w := by
  subst n
  have h : normalizeWord w.length w = w.get := by
    funext i
    simp [normalizeWord]
  rw [h]
  exact List.ofFn_get w

/-- An actual word-valued law supported at one length induces a finite law. -/
noncomputable def fixedLengthLaw (n : ℕ) (p : PMF Word) : PMF (FixedWord n) :=
  p.map (normalizeWord n)

/-- Normalization preserves an already fixed-length law exactly, not merely
approximately or after conditioning. -/
theorem fixedLengthLaw_map_toWord (n : ℕ) (p : PMF Word)
    (hp : ∀ w, p w ≠ 0 → w.length = n) :
    (fixedLengthLaw n p).map FixedWord.toWord = p := by
  classical
  rw [fixedLengthLaw, PMF.map_comp]
  conv_rhs => rw [← PMF.map_id p]
  ext y
  simp only [PMF.map_apply]
  apply tsum_congr
  intro w
  by_cases hw : p w = 0
  · simp only [hw, ite_self]
  · simp only [Function.comp_apply, normalizeWord_toWord w (hp w hw), id_eq]
    split_ifs <;> rfl

/-- The word-valued component and the paper's own-length mass agree. -/
theorem wordDistribution_mass (D : Ensemble) (y : Word) :
    D.wordDistribution y.length y = D.wordMass y := by
  classical
  simp only [Ensemble.wordDistribution, Ensemble.wordMass, Ensemble.prob, eventProb,
    PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : y = a.toWord
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

end AverageCaseComplexity.Completeness.TwoQuery
