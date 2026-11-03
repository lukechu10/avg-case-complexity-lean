module

public import AverageCaseComplexity.Distributions

@[expose] public section

/-!
# Semantic conditions for heuristic schemes (Itsykson §§2.3–2.4)

The accuracy argument is a positive index `k`, requesting error less than `1/k`.
These predicates describe correctness and usefulness only. They deliberately
make no computability or efficiency claim. In particular, they do not by
themselves define `AvgP`, `AvgBPP`, `HeurP`, or `HeurBPP`.
-/

namespace AverageCaseComplexity

abbrev DeterministicScheme := Word → Accuracy → Answer
abbrev RandomizedScheme := Word → Accuracy → PMF Answer

/-- A deterministic scheme, embedded into distribution semantics. -/
noncomputable def DeterministicScheme.randomize (A : DeterministicScheme) :
    RandomizedScheme := fun x δ => PMF.pure (A x δ)

/-- Probability of an incorrect Boolean answer; giving up is not an error here. -/
noncomputable def wrongProb (L : Language) (x : Word) (p : PMF Answer) : ENNReal :=
  eventProb p (fun a => ¬ IsAllowed L x a)

/-- Probability of failing to return the correct Boolean answer, including giving up. -/
noncomputable def failureProb (L : Language) (x : Word) (p : PMF Answer) : ENNReal :=
  eventProb p (fun a => a ≠ some (L x))

/-- Pointwise correctness is required only on the ensemble support. -/
def DeterministicScheme.Correct (A : DeterministicScheme)
    (P : DistributionalProblem) : Prop :=
  ∀ δ x, P.distribution.Supports x → IsAllowed P.language x (A x δ)

/-- Less than a `1/k` fraction of inputs give up at accuracy index `k`. -/
def DeterministicScheme.Useful (A : DeterministicScheme)
    (P : DistributionalProblem) : Prop :=
  ∀ δ n, P.distribution.prob n (fun x => A x δ = none) < δ.bound

/-- The semantic part of deterministic errorless heuristic schemes. -/
structure DeterministicScheme.ErrorlessConditions (A : DeterministicScheme)
    (P : DistributionalProblem) : Prop where
  correct : A.Correct P
  useful : A.Useful P

/-- General deterministic heuristic usefulness, allowing incorrect answers. -/
def DeterministicScheme.HeuristicConditions (A : DeterministicScheme)
    (P : DistributionalProblem) : Prop :=
  ∀ δ n, P.distribution.prob n (fun x => A x δ ≠ some (P.language x)) < δ.bound

/-- The randomized pointwise correctness condition of Definition 2.1. -/
def RandomizedScheme.Correct (A : RandomizedScheme)
    (P : DistributionalProblem) : Prop :=
  ∀ δ x, P.distribution.Supports x →
    wrongProb P.language x (A x δ) < (1 / 4 : ENNReal)

/-- Nested usefulness: input mass of large give-up probability is less than `1/k`. -/
def RandomizedScheme.Useful (A : RandomizedScheme)
    (P : DistributionalProblem) : Prop :=
  ∀ δ n, P.distribution.prob n (fun x => (1 / 4 : ENNReal) ≤ A x δ none) < δ.bound

/-- The semantic part of Definition 2.1, without its effectiveness condition. -/
structure RandomizedScheme.ErrorlessConditions (A : RandomizedScheme)
    (P : DistributionalProblem) : Prop where
  correct : A.Correct P
  useful : A.Useful P

/-- The nested error condition for general randomized heuristic schemes. -/
def RandomizedScheme.HeuristicConditions (A : RandomizedScheme)
    (P : DistributionalProblem) : Prop :=
  ∀ δ n, P.distribution.prob n
    (fun x => (1 / 4 : ENNReal) ≤ failureProb P.language x (A x δ)) < δ.bound

/-- Replace giving up by the Boolean answer `false`. -/
def DeterministicScheme.fillGiveUp (A : DeterministicScheme) : DeterministicScheme :=
  fun x δ => some ((A x δ).getD false)

/-- On supported inputs, an errorless deterministic scheme fails exactly when it gives up. -/
theorem DeterministicScheme.failure_iff_giveUp (A : DeterministicScheme)
    (P : DistributionalProblem) (h : A.Correct P) (δ : Accuracy)
    (x : Word) (hx : P.distribution.Supports x) :
    A x δ ≠ some (P.language x) ↔ A x δ = none := by
  rcases h δ x hx with hcorrect | hnone
  · simp [hcorrect]
  · simp [hnone]

/-- Forgetting errorlessness yields the general deterministic semantic condition.
This is only the probability part of `AvgP ⊆ HeurP`, not a runtime theorem. -/
theorem DeterministicScheme.ErrorlessConditions.toHeuristic
    {A : DeterministicScheme} {P : DistributionalProblem}
    (h : A.ErrorlessConditions P) : A.HeuristicConditions P := by
  classical
  intro δ n
  have heq : P.distribution.prob n (fun x => A x δ ≠ some (P.language x)) =
      P.distribution.prob n (fun x => A x δ = none) := by
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : P.distribution n w = 0
    · simp [hw]
    · simp only [A.failure_iff_giveUp P h.correct δ w.toWord ⟨n, w, rfl, hw⟩]
      split_ifs <;> rfl
  rw [heq]
  exact h.useful δ n

end AverageCaseComplexity
