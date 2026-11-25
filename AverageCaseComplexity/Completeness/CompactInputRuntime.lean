module

public import AverageCaseComplexity.Completeness.BoundedMachine
public import AverageCaseComplexity.Completeness.TupleDecodingRuntime

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
open Cslib.BitString Cslib.Kolmogorov

private theorem foldr_bit_pos_of_last_true : ∀ bits : Word,
    bits.getLast? = some true → 0 < bits.foldr Nat.bit 0
  | [], h => by simp at h
  | b :: tail, h => by
      cases tail with
      | nil =>
          simp only [List.getLast?_cons, List.getLast?_nil, Option.getD_none] at h
          cases b <;> simp_all [List.foldr, Nat.bit_val]
      | cons c rest =>
          have hlast : (c :: rest).getLast? = some true := by
            simpa [List.getLast?_cons] using h
          have hp := foldr_bit_pos_of_last_true (c :: rest) hlast
          change 0 < Nat.bit b ((c :: rest).foldr Nat.bit 0)
          rw [Nat.bit_val]
          omega

private theorem foldr_bit_bits_of_last_true (bits : Word)
    (h : bits.getLast? = some true) : (bits.foldr Nat.bit 0).bits = bits := by
  induction bits with
  | nil => simp at h
  | cons b tail ih =>
      cases tail with
      | nil =>
          simp only [List.getLast?_cons, List.getLast?_nil, Option.getD_none] at h
          have hb : b = true := Option.some.inj h
          subst b
          simp [List.foldr, Nat.bit]
      | cons c rest =>
          have hlast : (c :: rest).getLast? = some true := by
            simpa [List.getLast?_cons] using h
          have hpos := foldr_bit_pos_of_last_true (c :: rest) hlast
          have htail := ih hlast
          have hrepr :
              (Nat.bit b ((c :: rest).foldr Nat.bit 0)).bits =
                b :: ((c :: rest).foldr Nat.bit 0).bits :=
            Nat.bits_append_bit _ _ (by
              intro hz
              have : 0 < (c :: rest).foldr Nat.bit 0 := hpos
              omega)
          change (Nat.bit b ((c :: rest).foldr Nat.bit 0)).bits = b :: c :: rest
          rw [hrepr, htail]

private theorem nat_bits_last_true (n : ℕ) (hn : 0 < n) : n.bits.getLast? = some true := by
  induction n using Nat.binaryRec with
  | zero => simp at hn
  | bit b n ih =>
      have hb : n = 0 → b = true := by
        intro hn0
        subst n
        cases b <;> simp [Nat.bit_val] at hn ⊢
      have hbits := Nat.bits_append_bit n b hb
      rw [hbits]
      cases n with
      | zero =>
          have hb0 := hb rfl
          simp [Nat.bits, hb0]
      | succ n =>
          have htail : 0 < Nat.succ n := by omega
          have := ih htail
          simp [List.getLast?_cons, this]

private theorem binary_suffix_canonical_iff (bits : Word) :
    (∃ n, 0 < n ∧ n.bits = bits) ↔ bits.getLast? = some true := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact nat_bits_last_true n hn
  · intro h
    refine ⟨bits.foldr Nat.bit 0, foldr_bit_pos_of_last_true bits h,
      foldr_bit_bits_of_last_true bits h⟩

def boundedSchemeInputValue (x : Word) (k steps : ℕ) : Word :=
  let cap := steps + 1
  if k < cap then
    List.replicate k true ++ [false] ++ x.take (cap - (k + 1))
  else List.replicate cap true

@[fun_prop] theorem boundedSchemeInputValue_efficient :
    ComputableTidilyInPolyTime
      (fun q : (Word × ℕ) × ℕ => boundedSchemeInputValue q.1.1 q.1.2 q.2)
      (encPair (encPair encBits encUnary) encUnary) encBits := by
  let enc := encPair (encPair encBits encUnary) encUnary
  have hx := (fst encBits encUnary).comp (fst (encPair encBits encUnary) encUnary)
  have hk := (snd encBits encUnary).comp (fst (encPair encBits encUnary) encUnary)
  have hs := snd (encPair encBits encUnary) encUnary
  have hadd := unary_add
  have hcap : ComputableTidilyInPolyTime (fun q : (Word × ℕ) × ℕ => q.2 + 1) enc encUnary := by
    exact hadd.comp (hs.prod (const (encIn := enc) (encMid := encUnary) 1))
  have hk1 : ComputableTidilyInPolyTime (fun q : (Word × ℕ) × ℕ => q.1.2 + 1) enc encUnary := by
    exact hadd.comp (hk.prod (const (encIn := enc) (encMid := encUnary) 1))
  have htakeLen : ComputableTidilyInPolyTime
      (fun q : (Word × ℕ) × ℕ => q.2 + 1 - (q.1.2 + 1)) enc encUnary := by
    exact unary_sub.comp (hcap.prod hk1)
  have htake : ComputableTidilyInPolyTime
      (fun q : Word × ℕ => q.1.take q.2) (encPair encBits encUnary) encBits := by fun_prop
  have hbody := htake.comp (hx.prod htakeLen)
  have hrepK := (bitsReplicate true).comp hk
  have hrepCap := (bitsReplicate true).comp hcap
  have hyes := hrepK.bitsAppend ((const (encIn := enc) (encMid := encBits) [false]).bitsAppend hbody)
  have hcond : ComputableTidilyInPolyTime
      (fun q : (Word × ℕ) × ℕ => decide (q.1.2 < q.2 + 1)) enc encBool := by
    exact (unary_lt.comp (hk.prod hcap))
  have h := hcond.ite_decide hyes hrepCap
  exact h.of_enc_eq (fun q => by
    simp [boundedSchemeInputValue, Function.comp_apply])

private theorem boundedSchemeInput_value (x : Word) (k : Accuracy) (steps : ℕ) :
    boundedSchemeInput x k steps = boundedSchemeInputValue x k.val steps := by
  cases k
  rfl

private theorem boundedSchemeInput_capped (x : Word) (k : Accuracy) (steps : ℕ) :
    boundedSchemeInput x ⟨min (steps + 1) k.val,
      by have := k.property; omega⟩ steps = boundedSchemeInput x k steps := by
  by_cases hk : k.val < steps + 1
  · simp [boundedSchemeInput, hk, Nat.min_eq_right (Nat.le_of_lt hk)]
  · have hcap : steps + 1 ≤ k.val := by omega
    simp [boundedSchemeInput, hk, Nat.min_eq_left hcap]

/-- Construct the bounded candidate from a decoded header and raw suffix. -/
def compactInputCandidate (p : Word × (Word × Word)) (a : Word × Word) :
    Option (Word × Word) :=
  if a.2[a.2.length - 1]? = some true then
    let k := boundedBinaryValue (p.2.2.length + 1) a.2.reverse
    some (a.1, boundedSchemeInputValue p.2.1 k p.2.2.length)
  else none

/-- Parse a specialized code and materialize only the unary accuracy prefix
observable during the supplied coin-bounded run. The binary index is saturated
at `coins.length + 1` before constructing any unary word. -/
def compactInputRuntime (p : Word × (Word × Word)) : Option (Word × Word) :=
  if (decodeSDRuntime p.1).isSome then
    compactInputCandidate p ((decodeSDRuntime p.1).getD ([], []))
  else none

theorem compactInputRuntime_eq (code x coins : Word) :
    compactInputRuntime (code, (x, coins)) =
      (decodeSpecializedCode code).map
        (fun a => (a.1, boundedSchemeInput x a.2 coins.length)) := by
  unfold compactInputRuntime
  rw [decodeSDRuntime_eq_decodeSD code]
  cases hd : decodeSD code with
  | none => simp [decodeSpecializedCode, hd]
  | some pair =>
      rcases pair with ⟨header, bits⟩
      have hcanon := binary_suffix_canonical_iff bits
      by_cases hlast : bits.getLast? = some true
      · have hlastAt : bits[bits.length - 1]? = some true := by
          simpa only [List.getLast?_eq_getElem?] using hlast
        have hvalid : ∃ n, 0 < n ∧ n.bits = bits := hcanon.mpr hlast
        rcases hvalid with ⟨n, hn, hbits⟩
        have hfold : bits.foldr Nat.bit 0 = n := by
          have := congrArg (fun w : Word => w.foldr Nat.bit 0) hbits
          simpa using this.symm
        have hk :
            boundedBinaryValue (coins.length + 1) bits.reverse =
              min (coins.length + 1) n := by
          rw [boundedBinaryValue_eq, ← foldr_bit_eq_binaryValue_reverse, hfold]
        have hkpos : 0 < min (coins.length + 1) n := by omega
        have hbounded :
            boundedSchemeInputValue x
              (boundedBinaryValue (coins.length + 1) bits.reverse) coins.length =
              boundedSchemeInput x ⟨n, hn⟩ coins.length := by
          rw [hk, boundedSchemeInput_value]
          exact boundedSchemeInput_capped x ⟨n, hn⟩ coins.length
        have hdecode : decodeSpecializedCode code =
            some (header, ⟨n, hn⟩) := by
          unfold decodeSpecializedCode
          rw [hd]
          simp [hfold, hbits, hn]
        rw [hdecode]
        unfold compactInputCandidate
        simp [hlastAt, hbounded]
      · have hlastAt : bits[bits.length - 1]? ≠ some true := by
          intro h
          apply hlast
          simpa only [List.getLast?_eq_getElem?] using h
        have hnone : ¬ (0 < bits.foldr Nat.bit 0 ∧
            (bits.foldr Nat.bit 0).bits = bits) := by
          intro h
          exact hlast (hcanon.mp ⟨bits.foldr Nat.bit 0, h.1, h.2⟩)
        have hdecode : decodeSpecializedCode code = none := by
          unfold decodeSpecializedCode
          rw [hd]
          by_cases hp : 0 < bits.foldr Nat.bit 0
          · by_cases hb : (bits.foldr Nat.bit 0).bits = bits
            · exact False.elim (hnone ⟨hp, hb⟩)
            · simp [hp, hb]
          · simp [hp]
        rw [hdecode]
        unfold compactInputCandidate
        simp [hlastAt]

@[fun_prop] theorem compactInputCandidate_efficient :
    ComputableTidilyInPolyTime (fun q : (Word × (Word × Word)) × (Word × Word) =>
      compactInputCandidate q.1 q.2)
      (encPair (encPair encBits (encPair encBits encBits)) (encPair encBits encBits))
      (encOption (encPair encBits encBits)) := by
  let inputEnc := encPair (encPair encBits (encPair encBits encBits)) (encPair encBits encBits)
  have hargs : ComputableTidilyInPolyTime
      (fun q : (Word × (Word × Word)) × (Word × Word) =>
        ((q.1.2.1,
          boundedBinaryValue (q.1.2.2.length + 1) q.2.2.reverse),
          q.1.2.2.length)) inputEnc (encPair (encPair encBits encUnary) encUnary) := by
    fun_prop
  have hbounded := boundedSchemeInputValue_efficient.comp hargs
  have hhead : ComputableTidilyInPolyTime
      (fun q : (Word × (Word × Word)) × (Word × Word) => q.2.1) inputEnc encBits := by
    exact (fst encBits encBits).comp (snd
      (encPair encBits (encPair encBits encBits)) (encPair encBits encBits))
  have hpair : ComputableTidilyInPolyTime
      (fun q : (Word × (Word × Word)) × (Word × Word) =>
        (q.2.1, boundedSchemeInputValue q.1.2.1
          (boundedBinaryValue (q.1.2.2.length + 1) q.2.2.reverse)
          q.1.2.2.length)) inputEnc (encPair encBits encBits) :=
    hhead.prod hbounded
  have hsome := (optionSome (encPair encBits encBits)).comp hpair
  have hcheck : ComputableTidilyInPolyTime
      (fun q : (Word × (Word × Word)) × (Word × Word) =>
        decide (q.2.2[q.2.2.length - 1]? = some true)) inputEnc encBool := by
    fun_prop
  have h := hcheck.ite_decide hsome
    (const (encIn := inputEnc) (encMid := encOption (encPair encBits encBits)) none)
  exact h.of_enc_eq (fun q => by simp [compactInputCandidate])

@[fun_prop] theorem compactInputRuntime_efficient :
    ComputableTidilyInPolyTime compactInputRuntime
      (encPair encBits (encPair encBits encBits))
      (encOption (encPair encBits encBits)) := by
  have hdecode : ComputableTidilyInPolyTime
      (fun p : Word × (Word × Word) => decodeSDRuntime p.1)
      (encPair encBits (encPair encBits encBits))
      (encOption (encPair encBits encBits)) :=
    decodeSDRuntime_efficient.comp (fst encBits (encPair encBits encBits))
  have hget := optionGetDWithInput hdecode
    (const (encIn := encPair encBits (encPair encBits encBits))
      (encMid := encPair encBits encBits) ([], []))
  have hargs : ComputableTidilyInPolyTime
      (fun p : Word × (Word × Word) => (p, (decodeSDRuntime p.1).getD ([], [])))
      (encPair encBits (encPair encBits encBits))
      (encPair (encPair encBits (encPair encBits encBits)) (encPair encBits encBits)) :=
    (id' (encIn := encPair encBits (encPair encBits encBits))).prod hget
  have hcandidate := compactInputCandidate_efficient.comp hargs
  have hcheck : ComputableTidilyInPolyTime
      (fun p : Word × (Word × Word) => (decodeSDRuntime p.1).isSome)
      (encPair encBits (encPair encBits encBits)) encBool := by fun_prop
  exact hcheck.ite' hcandidate
    (const (encIn := encPair encBits (encPair encBits encBits))
      (encMid := encOption (encPair encBits encBits)) none)

end AverageCaseComplexity.Completeness.TwoQuery
