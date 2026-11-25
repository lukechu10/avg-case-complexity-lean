module

public import AverageCaseComplexity.Completeness.EncodingRuntime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
open Cslib.BitString Cslib.Kolmogorov

theorem foldr_bit_eq_binaryValue_reverse (w : Word) :
    w.foldr Nat.bit 0 = binaryValue w.reverse := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      simp only [List.foldr_cons, List.reverse_cons, List.foldl_append, binaryValue] at ih ⊢
      cases b <;> simp [Nat.bit, ih]

/-- The suffix length field is accumulated with a cap at the available input size.
This prevents a malformed binary length from forcing exponentially large unary work. -/
def decodeSelfDelimitingBounded (w : Word) : Word × Word :=
  let k := w.idxOf false
  let r := w.drop (k + 1)
  let n := boundedBinaryValue r.length ((r.take k).reverse)
  let body := r.drop k
  (body.take n, body.drop n)

/-- The saturating, input-bounded implementation of the total self-delimiting
split is tidy polynomial time. -/
@[fun_prop] theorem decodeSelfDelimitingBounded_efficient :
    ComputableTidilyInPolyTime decodeSelfDelimitingBounded encBits
      (encPair encBits encBits) := by
  unfold decodeSelfDelimitingBounded
  fun_prop

theorem decodeSelfDelimitingBounded_eq (w : Word) :
    decodeSelfDelimitingBounded w = decodeSelfDelimiting w := by
  unfold decodeSelfDelimitingBounded decodeSelfDelimiting
  dsimp
  let k := w.idxOf false
  let r := w.drop (k + 1)
  let n := (r.take k).foldr Nat.bit 0
  let body := r.drop k
  have hn : boundedBinaryValue r.length ((r.take k).reverse) = min r.length n := by
    rw [boundedBinaryValue_eq, ← foldr_bit_eq_binaryValue_reverse]
  change (body.take (boundedBinaryValue r.length ((r.take k).reverse)),
    body.drop (boundedBinaryValue r.length ((r.take k).reverse))) =
      (body.take n, body.drop n)
  rw [hn]
  by_cases h : n ≤ r.length
  · rw [Nat.min_eq_right h]
  · have hdrop : body.length ≤ r.length := by
      simp [body]
    have hbody : body.length ≤ n := le_trans hdrop (le_of_lt (lt_of_not_ge h))
    have hmin : min r.length n = r.length := Nat.min_eq_left (le_of_lt (lt_of_not_ge h))
    rw [hmin]
    apply Prod.ext
    · calc
        body.take r.length = body := List.take_of_length_le hdrop
        _ = body.take n := (List.take_of_length_le hbody).symm
    · calc
        body.drop r.length = [] := List.drop_eq_nil_of_le hdrop
        _ = body.drop n := (List.drop_eq_nil_of_le hbody).symm

/-- The runtime-oriented checked version of `decodeSD`. -/
def decodeSDRuntime (w : Word) : Option (Word × Word) :=
  if w.idxOf false < w.length then
    let pair := decodeSelfDelimitingBounded w
    if selfDelimitingCode pair.1 ++ pair.2 = w then some pair else none
  else none

theorem decodeSDRuntime_eq_decodeSD (w : Word) : decodeSDRuntime w = decodeSD w := by
  simp [decodeSDRuntime, decodeSD, List.idxOf_lt_length_iff, decodeSelfDelimitingBounded_eq]

@[fun_prop] theorem decodeSDRuntime_efficient :
    ComputableTidilyInPolyTime decodeSDRuntime encBits
      (encOption (encPair encBits encBits)) := by
  unfold decodeSDRuntime
  fun_prop

@[fun_prop] theorem decodeSD_efficient :
    ComputableTidilyInPolyTime decodeSD encBits
      (encOption (encPair encBits encBits)) := by
  exact decodeSDRuntime_efficient.of_enc_eq (fun w =>
    congrArg (encOption (encPair encBits encBits)) (decodeSDRuntime_eq_decodeSD w).symm)

/-- Speculatively split every field; a single final re-encoding check will
reject malformed input. The candidate itself is total, including on `[]`. -/
def seedCandidate (w : Word) : Seed :=
  let a := decodeSelfDelimitingBounded w
  let b := decodeSelfDelimitingBounded a.2
  let c := decodeSelfDelimitingBounded b.2
  let d := decodeSelfDelimitingBounded (c.2.drop 1)
  ⟨a.1, b.1, c.1, decide (c.2.take 1 = [true]), d.1, d.2⟩

@[simp] theorem seedCandidate_encodeSeed (s : Seed) : seedCandidate (encodeSeed s) = s := by
  cases s with
  | mk a b c bit d e => cases bit <;>
      simp [seedCandidate, encodeSeed, decodeSelfDelimitingBounded_eq, List.append_assoc,
        decodeSelfDelimiting_selfDelimitingCode_append]

/-- The external seed encoding can also serve as an injective machine output encoding. -/
def seedEncoding : Seed ↪ Word := ⟨encodeSeed, fun a b h => by
  simpa using congrArg seedCandidate h⟩

theorem seedCandidate_fields :
    ComputableTidilyInPolyTime (fun w => (seedCandidate w).machineCode) encBits encBits ∧
    ComputableTidilyInPolyTime (fun w => (seedCandidate w).input) encBits encBits ∧
    ComputableTidilyInPolyTime (fun w => (seedCandidate w).clockBits) encBits encBits ∧
    ComputableTidilyInPolyTime (fun w => (seedCandidate w).fallback) encBits encBool ∧
    ComputableTidilyInPolyTime (fun w => (seedCandidate w).samplerCode) encBits encBits ∧
    ComputableTidilyInPolyTime (fun w => (seedCandidate w).samplerClockBits) encBits encBits := by
    have a := decodeSelfDelimitingBounded_efficient
    have b := a.comp a.snd'
    have c := a.comp b.snd'
    have dropOne : ComputableTidilyInPolyTime (List.drop 1 : Word → Word) encBits encBits := by fun_prop
    have takeOne : ComputableTidilyInPolyTime (List.take 1 : Word → Word) encBits encBits := by fun_prop
    have d := a.comp (dropOne.comp c.snd')
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [seedCandidate]
    · exact a.fst'
    · exact b.fst'
    · exact c.fst'
    · exact (takeOne.comp c.snd').decide_eq' (.const [true])
    · exact d.fst'
    · exact d.snd'

@[fun_prop] theorem seedCandidate_efficient :
    ComputableTidilyInPolyTime seedCandidate encBits seedEncoding := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := seedCandidate_fields
  exact (encodeSeed_efficient_with ha hb hc hd he hf).of_enc_eq (fun _ => rfl)

private theorem checkCandidate {α : Type} (code : α ↪ Word) (candidate : Word → α)
    (parse : Word → Option α) (roundtrip : ∀ a, candidate (code a) = a)
    (complete : ∀ a, parse (code a) = some a)
    (sound : ∀ w a, parse w = some a → code a = w)
    (hc : ComputableTidilyInPolyTime candidate encBits code) :
    ComputableTidilyInPolyTime parse encBits (encOption code) := by
  have hc' : ComputableTidilyInPolyTime (fun w => code (candidate w)) encBits encBits :=
    hc.of_enc_eq (fun _ => rfl)
  let checked := fun w => if code (candidate w) = w then some (candidate w) else none
  have he : ComputableTidilyInPolyTime checked encBits (encOption code) := by
    exact (hc'.decide_eq' (.id' (encIn := encBits))).ite_decide ((optionSome code).comp hc) (.const none)
  apply he.of_enc_eq
  intro w
  apply congrArg
  unfold checked
  split_ifs with h
  · exact (complete (candidate w) ▸ congrArg parse h).symm
  · cases hw : parse w with
    | none => rfl
    | some a => exact (h (by rw [← sound w a hw, roundtrip])).elim

@[fun_prop] theorem decodeSeed_efficient :
    ComputableTidilyInPolyTime decodeSeed encBits (encOption seedEncoding) :=
  checkCandidate seedEncoding seedCandidate decodeSeed seedCandidate_encodeSeed
    decodeSeed_encodeSeed decodeSeed_encodeSeed_eq seedCandidate_efficient

/-- Interpret the lengths, not contents, of both padded clock fields. -/
def instanceCandidate (w : Word) : Instance :=
  let s := seedCandidate w
  ⟨s.machineCode, s.input, s.clockBits.length, s.fallback, s.samplerCode, s.samplerClockBits.length⟩

@[simp] theorem instanceCandidate_encode (z : Instance) : instanceCandidate (encode z) = z := by
  cases z
  simp [instanceCandidate, encode, Instance.seed]

def instanceEncoding : Instance ↪ Word := ⟨encode, encode_injective⟩

@[fun_prop] theorem instanceCandidate_efficient :
    ComputableTidilyInPolyTime instanceCandidate encBits instanceEncoding := by
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := seedCandidate_fields
  have clock (f : Word → Word) (h : ComputableTidilyInPolyTime f encBits encBits) :
      ComputableTidilyInPolyTime (fun w => List.replicate (f w).length true) encBits encBits := by
    simpa only [Function.comp_def] using (bitsReplicate true).comp (length_bits.comp h)
  have h : ComputableTidilyInPolyTime (fun w => encodeSeed (instanceCandidate w).seed)
      encBits encBits := by
    apply encodeSeed_efficient_with (seed := fun w => (instanceCandidate w).seed)
    all_goals dsimp only [Instance.seed, instanceCandidate]
    · exact ha
    · exact hb
    · exact clock (fun w => (seedCandidate w).clockBits) hc
    · exact hd
    · exact he
    · exact clock (fun w => (seedCandidate w).samplerClockBits) hf
  exact h.of_enc_eq (fun _ => rfl)

@[fun_prop] theorem decode_efficient :
    ComputableTidilyInPolyTime decode encBits (encOption instanceEncoding) :=
  checkCandidate instanceEncoding instanceCandidate decode instanceCandidate_encode
    decode_encode decode_sound instanceCandidate_efficient

end AverageCaseComplexity.Completeness.TwoQuery
