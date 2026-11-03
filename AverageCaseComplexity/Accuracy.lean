module

public import AverageCaseComplexity.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Unary reciprocal accuracy

A positive integer `k` asks for error less than `1/k`. Input `(x,k)` is encoded
as `1^k 0 x`. Its length is `|x| + k + 1`, including at input length zero.
Rational approximation below is a statement about numerical bounds, not a
runtime claim for reading arbitrary rational encodings.
-/

namespace AverageCaseComplexity

/-- The rational error bound requested by an index. -/
def Accuracy.rational (k : Accuracy) : ℚ := 1 / (k.val : ℚ)

theorem Accuracy.rational_pos (k : Accuracy) : 0 < k.rational := by
  exact div_pos zero_lt_one (by exact_mod_cast k.property)

theorem Accuracy.rational_le_one (k : Accuracy) : k.rational ≤ 1 := by
  have hk : (1 : ℚ) ≤ k.val := by exact_mod_cast k.property
  exact (div_le_one (by positivity : (0 : ℚ) < k.val)).mpr hk

/-- A reciprocal accuracy is also a valid rational accuracy. -/
def Accuracy.toRationalAccuracy (k : Accuracy) : RationalAccuracy :=
  ⟨k.rational, k.rational_pos, k.rational_le_one⟩

/-- Round a requested rational accuracy down to a reciprocal accuracy. -/
def RationalAccuracy.reciprocalIndex (δ : RationalAccuracy) : Accuracy :=
  ⟨⌈1 / δ.val⌉₊, Nat.ceil_pos.mpr (div_pos zero_lt_one δ.property.1)⟩

/-- The reciprocal request is at least as stringent as the original request. -/
theorem RationalAccuracy.reciprocalIndex_le (δ : RationalAccuracy) :
    δ.reciprocalIndex.rational ≤ δ.val := by
  have hk : (0 : ℚ) < δ.reciprocalIndex.val := by
    exact_mod_cast δ.reciprocalIndex.property
  apply (one_div_le hk δ.property.1).mpr
  exact Nat.le_ceil (1 / δ.val)

/-- Rounding increases the reciprocal resource parameter by less than one. -/
theorem RationalAccuracy.reciprocalIndex_lt (δ : RationalAccuracy) :
    (δ.reciprocalIndex.val : ℚ) < 1 / δ.val + 1 :=
  Nat.ceil_lt_add_one (le_of_lt (div_pos zero_lt_one δ.property.1))

/-- Unary reciprocal-accuracy input, with a zero delimiter before the input word. -/
def encodeSchemeInput (x : Word) (k : Accuracy) : Word :=
  List.replicate k.val true ++ false :: x

@[simp] theorem encodeSchemeInput_length (x : Word) (k : Accuracy) :
    (encodeSchemeInput x k).length = x.length + k.val + 1 := by
  simp [encodeSchemeInput]
  omega

private theorem unary_delimited_injective (k l : ℕ) (x y : Word)
    (h : List.replicate k true ++ false :: x = List.replicate l true ++ false :: y) :
    k = l ∧ x = y := by
  induction k generalizing l with
  | zero =>
    cases l with
    | zero => simpa using h
    | succ l => simp [List.replicate_succ] at h
  | succ k ih =>
    cases l with
    | zero => simp [List.replicate_succ] at h
    | succ l =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨hkl, hxy⟩ := ih l h
      exact ⟨congrArg Nat.succ hkl, hxy⟩

/-- A fixed injective encoding usable with machine-level runtime certificates. -/
def schemeInputEncoding : (Word × Accuracy) ↪ Word where
  toFun a := encodeSchemeInput a.1 a.2
  inj' := by
    rintro ⟨x, k⟩ ⟨y, l⟩ h
    obtain ⟨hkl, hxy⟩ := unary_delimited_injective k.val l.val x y h
    exact Prod.ext hxy (Subtype.ext hkl)

/-- At positive lengths the encoded size is linearly bounded by `n*k`.
Polynomial bounds in encoded length therefore fit the paper's `poly(n/δ)`. -/
theorem encodeSchemeInput_length_le (x : Word) (k : Accuracy) (hx : 0 < x.length) :
    (encodeSchemeInput x k).length ≤ 3 * (x.length * k.val) := by
  rw [encodeSchemeInput_length]
  have hn : x.length ≤ x.length * k.val := Nat.le_mul_of_pos_right _ k.property
  have hk : k.val ≤ x.length * k.val := Nat.le_mul_of_pos_left _ hx
  omega

/-- Conversely, `n*k` is at most quadratic in the encoded size. -/
theorem size_product_le_encoding_sq (x : Word) (k : Accuracy) :
    x.length * k.val ≤ (encodeSchemeInput x k).length ^ 2 := by
  rw [encodeSchemeInput_length, pow_two]
  exact Nat.mul_le_mul (by omega) (by omega)

end AverageCaseComplexity
