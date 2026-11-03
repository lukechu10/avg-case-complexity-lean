module

public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-!
# Basic objects for distributional decision problems

We include length zero. Executable schemes use a positive integer `k` requesting
error less than `1/k`, with `k` encoded in unary. Rational accuracies are retained
separately for comparison with the paper's notation.
-/

namespace AverageCaseComplexity

abbrev Word := List Bool
abbrev FixedWord (n : ℕ) := Fin n → Bool
abbrev Language := Word → Bool

/-- Convert a length-indexed word to the machine-input representation. -/
def FixedWord.toWord {n : ℕ} (x : FixedWord n) : Word := List.ofFn x

@[simp] theorem FixedWord.length_toWord {n : ℕ} (x : FixedWord n) :
    x.toWord.length = n := by simp [FixedWord.toWord]

/-- `none` means giving up; `some b` means answering the bit `b`. -/
abbrev Answer := Option Bool

/-- A rational accuracy as in the paper; not the executable input representation. -/
abbrev RationalAccuracy := {δ : ℚ // 0 < δ ∧ δ ≤ 1}

/-- A positive reciprocal-accuracy index. Index `k` requests error less than `1/k`. -/
abbrev Accuracy := {k : ℕ // 0 < k}

/-- An answer is allowed by deterministic errorless correctness. -/
def IsAllowed (L : Language) (x : Word) (a : Answer) : Prop :=
  a = some (L x) ∨ a = none

end AverageCaseComplexity
