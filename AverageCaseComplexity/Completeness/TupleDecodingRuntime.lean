module

public import AverageCaseComplexity.Completeness.EncodingRuntime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
open Cslib.BitString Cslib.Kolmogorov

private theorem foldr_bit_eq_binaryValue_reverse (w : Word) :
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

private theorem decodeSelfDelimitingBounded_eq (w : Word) :
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

end AverageCaseComplexity.Completeness.TwoQuery
