module

public import AverageCaseComplexity.Accuracy
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-! # Distribution ensembles (Itsykson §2.2) -/

namespace AverageCaseComplexity

/-- Exact length-indexed probability distributions, including length zero. -/
abbrev Ensemble := (n : ℕ) → PMF (FixedWord n)

/-- Finite event probability. No decidability assumption on the event is needed. -/
noncomputable def eventProb {α : Type*} [Fintype α] (p : PMF α)
    (event : α → Prop) : ENNReal := by
  classical
  exact ∑ x, if event x then p x else 0

@[simp] theorem eventProb_false {α : Type*} [Fintype α] (p : PMF α) :
    eventProb p (fun _ => False) = 0 := by simp [eventProb]

@[simp] theorem eventProb_true {α : Type*} [Fintype α] (p : PMF α) :
    eventProb p (fun _ => True) = 1 := by
  simpa [eventProb, tsum_fintype] using p.tsum_coe

/-- Event probability at a specified input length. -/
noncomputable def Ensemble.prob (D : Ensemble) (n : ℕ)
    (event : Word → Prop) : ENNReal :=
  eventProb (D n) (fun x => event x.toWord)

/-- The ensemble support, viewed as a set of ordinary finite words. -/
def Ensemble.Supports (D : Ensemble) (x : Word) : Prop :=
  ∃ (n : ℕ) (w : FixedWord n), w.toWord = x ∧ D n w ≠ 0

/-- An event has zero probability if it contains no supported input. -/
theorem Ensemble.prob_eq_zero_of_not_support (D : Ensemble) (n : ℕ)
    (event : Word → Prop) (h : ∀ x, D.Supports x → ¬ event x) :
    D.prob n event = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : D n w = 0
  · simp [hw]
  · simp [h w.toWord ⟨n, w, rfl, hw⟩]

/-- A language supplied with an input distribution ensemble. -/
structure DistributionalProblem where
  language : Language
  distribution : Ensemble

/-- The uniform ensemble: each length-`n` word has mass `1 / 2^n`. -/
noncomputable def uniformEnsemble : Ensemble := fun n =>
  PMF.ofFintype (fun _ => (Fintype.card (FixedWord n) : ENNReal)⁻¹) (by
    simp [ENNReal.mul_inv_cancel])

@[simp] theorem uniformEnsemble_apply (n : ℕ) (x : FixedWord n) :
    uniformEnsemble n x = (2 ^ n : ENNReal)⁻¹ := by
  simp [uniformEnsemble]

/-- Interpret the reciprocal accuracy `1/k` as a probability bound. -/
noncomputable def Accuracy.bound (k : Accuracy) : ENNReal := (k.val : ENNReal)⁻¹

@[simp] theorem Accuracy.bound_pos (k : Accuracy) : 0 < k.bound := by
  simp [Accuracy.bound]

@[simp] theorem Accuracy.bound_ne_zero (k : Accuracy) : k.bound ≠ 0 :=
  ne_of_gt k.bound_pos

end AverageCaseComplexity
