module

public import AverageCaseComplexity.Basic
public import Complexity.Computability.Kolmogorov.SelfDelimiting
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

/-- Canonical query tuple (M,x,1^m,b,S,1^s). -/
structure Instance where
  machineCode : Word
  input : Word
  steps : ℕ
  fallback : Bool
  samplerCode : Word
  samplerSteps : ℕ

/-- Raw seed tuple (M,y,r,b,S,σ), before canonicalization. -/
structure Seed where
  machineCode : Word
  input : Word
  clockBits : Word
  fallback : Bool
  samplerCode : Word
  samplerClockBits : Word

open Cslib.Kolmogorov

/-- One canonical self-delimiting field, followed by an unframed suffix.
The library decoder is total, so the equality check rejects malformed prefixes. -/
def decodeSD (w : Word) : Option (Word × Word) :=
  if false ∈ w then
    let (p, suffix) := decodeSelfDelimiting w
    if selfDelimitingCode p ++ suffix = w then some (p, suffix) else none
  else none

theorem selfDelimitingCode_has_false (p : Word) : false ∈ selfDelimitingCode p := by
  simp [selfDelimitingCode]

theorem decodeSD_encodeSD_append (p suffix : Word) :
    decodeSD (selfDelimitingCode p ++ suffix) = some (p, suffix) := by
  simp [decodeSD, selfDelimitingCode_has_false, decodeSelfDelimiting_selfDelimitingCode_append]

theorem decodeSD_sound {w p suffix : Word} (h : decodeSD w = some (p, suffix)) :
    selfDelimitingCode p ++ suffix = w := by
  by_cases hmem : false ∈ w
  · simp [decodeSD, hmem] at h
    rcases h with ⟨hcode, hpair⟩
    cases hpair
    exact hcode
  · simp [decodeSD, hmem] at h

def encodeSeed (z : Seed) : Word :=
  selfDelimitingCode z.machineCode ++ selfDelimitingCode z.input ++
    selfDelimitingCode z.clockBits ++ [z.fallback] ++
    selfDelimitingCode z.samplerCode ++ z.samplerClockBits

def decodeSeedCore (w : Word) : Option Seed := do
  let (machineCode, w) ← decodeSD w
  let (input, w) ← decodeSD w
  let (clockBits, w) ← decodeSD w
  match w with
  | [] => none
  | fallback :: w => do
      let (samplerCode, samplerClockBits) ← decodeSD w
      some ⟨machineCode, input, clockBits, fallback, samplerCode, samplerClockBits⟩

def decodeSeed (w : Word) : Option Seed :=
  match decodeSeedCore w with
  | none => none
  | some z => if encodeSeed z = w then some z else none

def Instance.seed (z : Instance) : Seed :=
  ⟨z.machineCode, z.input, List.replicate z.steps true, z.fallback,
    z.samplerCode, List.replicate z.samplerSteps true⟩

def encode (z : Instance) : Word := encodeSeed z.seed

def decode (w : Word) : Option Instance := do
  let z ← decodeSeed w
  if z.clockBits = List.replicate z.clockBits.length true ∧
      z.samplerClockBits = List.replicate z.samplerClockBits.length true then
    some ⟨z.machineCode, z.input, z.clockBits.length, z.fallback,
      z.samplerCode, z.samplerClockBits.length⟩
  else none

theorem decodeSeedCore_encodeSeed (z : Seed) : decodeSeedCore (encodeSeed z) = some z := by
  simp [decodeSeedCore, encodeSeed, List.append_assoc, decodeSD_encodeSD_append]

theorem decodeSeed_encodeSeed (z : Seed) : decodeSeed (encodeSeed z) = some z := by
  simp [decodeSeed, decodeSeedCore_encodeSeed]

theorem decode_encode (z : Instance) : decode (encode z) = some z := by
  simp [decode, encode, Instance.seed, decodeSeed_encodeSeed]

theorem encode_injective : Function.Injective encode := by
  intro u v h
  have hh := congrArg decode h
  rw [decode_encode, decode_encode] at hh
  exact Option.some.inj hh

theorem decodeSeed_ones (n : ℕ) : decodeSeed (List.replicate n true) = none := by
  simp [decodeSeed, decodeSeedCore, decodeSD]

theorem encode_ne_ones (z : Instance) (n : ℕ) : encode z ≠ List.replicate n true := by
  intro h
  have hh : decodeSeed (encodeSeed z.seed) = decodeSeed (List.replicate n true) :=
    congrArg decodeSeed h
  rw [decodeSeed_encodeSeed, decodeSeed_ones] at hh
  cases hh

theorem decodeSeed_encodeSeed_eq (w : Word) (z : Seed) (h : decodeSeed w = some z) :
    encodeSeed z = w := by
  unfold decodeSeed at h
  cases hc : decodeSeedCore w with
  | none => simp [hc] at h
  | some z' =>
      simp only [hc] at h
      split_ifs at h with heq
      simp_all

/-- Successful instance parsing reconstructs the entire input, including
canonical unary clocks; there are no accepted alternative tuple spellings. -/
theorem decode_sound (w : Word) (z : Instance) (h : decode w = some z) : encode z = w := by
  unfold decode at h
  cases hd : decodeSeed w with
  | none => simp [hd] at h
  | some seed =>
      simp only [hd] at h
      dsimp at h
      split_ifs at h with hu
      have heq := Option.some.inj h
      cases heq
      change encodeSeed
        ⟨seed.machineCode, seed.input, List.replicate seed.clockBits.length true,
          seed.fallback, seed.samplerCode, List.replicate seed.samplerClockBits.length true⟩ = w
      rw [← hu.1, ← hu.2]
      exact decodeSeed_encodeSeed_eq w seed hd

theorem encodeSeed_length_congr (u v : Seed)
    (hM : u.machineCode.length = v.machineCode.length)
    (hx : u.input.length = v.input.length)
    (hm : u.clockBits.length = v.clockBits.length)
    (hS : u.samplerCode.length = v.samplerCode.length)
    (hs : u.samplerClockBits.length = v.samplerClockBits.length) :
    (encodeSeed u).length = (encodeSeed v).length := by
  simp [encodeSeed, length_selfDelimitingCode, hM, hx, hm, hS, hs]

/-- Exact length formula: four self-delimiting fields, one Boolean delimiter,
and a raw final suffix. This gives logarithmic additive overhead in each of the
four framed field lengths. -/
theorem encodeSeed_length_eq (z : Seed) :
    (encodeSeed z).length = z.machineCode.length + z.input.length + z.clockBits.length + 1 +
      z.samplerCode.length + z.samplerClockBits.length +
      2 * z.machineCode.length.size + 2 * z.input.length.size +
      2 * z.clockBits.length.size + 2 * z.samplerCode.length.size + 4 := by
  simp [encodeSeed, length_selfDelimitingCode]
  omega

/-- Coarse logarithmic-overhead bound used by the parent construction. -/
theorem encodeSeed_length_le (z : Seed) :
    (encodeSeed z).length ≤
      z.machineCode.length + z.input.length + z.clockBits.length + 1 +
      z.samplerCode.length + z.samplerClockBits.length +
      10 * (Nat.log2 (z.machineCode.length + z.input.length +
        z.clockBits.length + z.samplerCode.length + 2) + 1) + 5 := by
  rw [encodeSeed_length_eq]
  let N := z.machineCode.length + z.input.length + z.clockBits.length + z.samplerCode.length + 2
  have hN : N ≠ 0 := by dsimp [N]; omega
  have hpow : N < 2 ^ (Nat.log2 N + 1) := by
    rw [Nat.log2_eq_log_two]
    apply (Nat.log_lt_iff_lt_pow Nat.one_lt_two hN).mp
    omega
  have hM : z.machineCode.length.size ≤ Nat.log2 N + 1 := by
    apply Nat.size_le.mpr
    dsimp [N] at hpow ⊢
    omega
  have hx : z.input.length.size ≤ Nat.log2 N + 1 := by
    apply Nat.size_le.mpr
    dsimp [N] at hpow ⊢
    omega
  have hr : z.clockBits.length.size ≤ Nat.log2 N + 1 := by
    apply Nat.size_le.mpr
    dsimp [N] at hpow ⊢
    omega
  have hS : z.samplerCode.length.size ≤ Nat.log2 N + 1 := by
    apply Nat.size_le.mpr
    dsimp [N] at hpow ⊢
    omega
  dsimp [N] at *
  omega

theorem payload_length_le_encode_length (z : Instance) :
    z.machineCode.length + z.input.length + z.steps + 1 +
      z.samplerCode.length + z.samplerSteps ≤ (encode z).length := by
  simp [encode, encodeSeed, Instance.seed, length_selfDelimitingCode]
  omega

theorem input_length_le_encode_length (z : Instance) :
    z.input.length ≤ (encode z).length := by
  have h := payload_length_le_encode_length z
  omega

end AverageCaseComplexity.Completeness.TwoQuery
