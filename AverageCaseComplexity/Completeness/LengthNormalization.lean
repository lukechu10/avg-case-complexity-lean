module

public import AverageCaseComplexity.Sampling

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

end AverageCaseComplexity.Completeness.TwoQuery
