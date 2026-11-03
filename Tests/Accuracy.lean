import AverageCaseComplexity
import Mathlib.Tactic.NormNum

open AverageCaseComplexity

-- The largest allowed error request is still represented by k = 1.
example : Accuracy.rational ⟨1, by decide⟩ = 1 := by
  norm_num [Accuracy.rational]

-- Rounding a nonreciprocal request down: 2/5 becomes 1/3.
example : (RationalAccuracy.reciprocalIndex ⟨2 / 5, by constructor <;> norm_num⟩).val = 3 := by
  change ⌈(1 / (2 / 5) : ℚ)⌉₊ = 3
  apply (Nat.ceil_eq_iff (by decide)).mpr
  norm_num

example : (RationalAccuracy.reciprocalIndex ⟨1, by constructor <;> norm_num⟩).val = 1 := by
  change ⌈(1 / 1 : ℚ)⌉₊ = 1
  apply (Nat.ceil_eq_iff (by decide)).mpr
  norm_num

-- The first zero is an unambiguous delimiter, even if x begins with ones.
example : encodeSchemeInput [true, false] ⟨2, by decide⟩ =
    [true, true, false, true, false] := rfl

-- Length-zero inputs have a nonempty, positive-size machine representation.
example : (encodeSchemeInput [] ⟨1, by decide⟩).length = 2 := rfl

-- Scheme usefulness uses the reciprocal of the index, not the index itself.
example : Accuracy.bound ⟨4, by decide⟩ = (1 / 4 : ENNReal) := by
  simp [Accuracy.bound]

-- Encoding injectivity preserves both the word and accuracy index.
example (a b : Word × Accuracy) (h : schemeInputEncoding a = schemeInputEncoding b) :
    a = b := schemeInputEncoding.injective h
