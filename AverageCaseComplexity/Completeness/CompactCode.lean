module

public import AverageCaseComplexity.Completeness.EncodingRuntime

@[expose] public section

/-! # Compact binary accuracy specialization

This is the representation layer of source compilation, not the universal
interpreter or semantic compilation theorem. A fixed self-delimited machine
header is followed by a raw binary accuracy suffix. Framing or duplicating each
accuracy bit would invalidate the sharp linear exponential-size bound.
-/

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM Cslib.Kolmogorov

def specializeCode (header : Word) (k : Accuracy) : Word :=
  selfDelimitingCode header ++ k.val.bits

def decodeSpecializedCode (w : Word) : Option (Word × Accuracy) := do
  let (header, bits) ← decodeSD w
  let index := bits.foldr Nat.bit 0
  if h : 0 < index then
    if index.bits = bits then some (header, ⟨index, h⟩) else none
  else none

@[simp] theorem decodeSpecializedCode_specializeCode (header : Word) (k : Accuracy) :
    decodeSpecializedCode (specializeCode header k) = some (header, k) := by
  simp [decodeSpecializedCode, specializeCode, decodeSD_encodeSD_append, k.property]

/-- Successful parsing checks the spelling of both the fixed header and
binary suffix; redundant high zero bits are rejected. -/
theorem decodeSpecializedCode_sound (w header : Word) (k : Accuracy)
    (h : decodeSpecializedCode w = some (header, k)) : specializeCode header k = w := by
  unfold decodeSpecializedCode at h
  cases hd : decodeSD w with
  | none => simp [hd] at h
  | some pair =>
      rcases pair with ⟨header', bits⟩
      simp only [hd] at h
      dsimp at h
      split_ifs at h with hpos hbits
      have heq := Option.some.inj h
      have hheader : header' = header := congrArg Prod.fst heq
      have hindex : bits.foldr Nat.bit 0 = k.val := congrArg (fun a => a.2.val) heq
      have hraw := decodeSD_sound hd
      rw [hheader, ← hbits, hindex] at hraw
      exact hraw

theorem specializeCode_injective :
    Function.Injective (fun a : Word × Accuracy => specializeCode a.1 a.2) := by
  intro a b h
  have hh := congrArg decodeSpecializedCode h
  simpa only [decodeSpecializedCode_specializeCode, Option.some.injEq] using hh

@[simp] theorem specializeCode_length (header : Word) (k : Accuracy) :
    (specializeCode header k).length = (selfDelimitingCode header).length + k.val.size := by
  simp [specializeCode, Nat.size_eq_bits_len]

/-- The variable binary suffix has coefficient one on log k. -/
theorem specializeCode_size (header : Word) (k : Accuracy) :
    2 ^ (specializeCode header k).length ≤
      2 ^ ((selfDelimitingCode header).length + 1) * (k.val + 1) := by
  have hs : 0 < k.val.size := Nat.size_pos.mpr k.property
  have hp : 2 ^ (k.val.size - 1) ≤ k.val := Nat.lt_size.mp (by omega)
  have hpow : 2 ^ k.val.size ≤ 2 * (k.val + 1) := by
    calc
      2 ^ k.val.size = 2 ^ (k.val.size - 1) * 2 := by
        rw [← Nat.pow_succ]
        congr 1
        omega
      _ ≤ k.val * 2 := Nat.mul_le_mul_right 2 hp
      _ ≤ _ := by omega
  rw [specializeCode_length, Nat.pow_add, Nat.pow_succ]
  calc
    _ ≤ 2 ^ (selfDelimitingCode header).length * (2 * (k.val + 1)) :=
      Nat.mul_le_mul_left _ hpow
    _ = _ := by ring

/-- Construct the raw binary suffix from the actual unary accuracy input,
charging for that conversion with the library's machine certificate. -/
theorem specializeCode_efficient (header : Word) :
    ComputableTidilyInPolyTime (fun a : Word × Accuracy => specializeCode header a.2)
      schemeInputEncoding encBits := by
  have hk := schemeInput_index_efficient
  have hbits : ComputableTidilyInPolyTime (fun a : Word × Accuracy => a.2.val.bits)
      schemeInputEncoding encBits :=
    (ComputableTidilyInPolyTime.unary_to_binary.comp hk).of_enc_eq
      (fun a => by simp [encNat_apply])
  exact (ComputableTidilyInPolyTime.const (selfDelimitingCode header)).bitsAppend hbits

end AverageCaseComplexity.Completeness.TwoQuery
