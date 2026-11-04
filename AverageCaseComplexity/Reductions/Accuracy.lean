module

public import AverageCaseComplexity.Reductions.Definitions
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

@[expose] public section

namespace AverageCaseComplexity

open Turing.MultiTapeTM

/-- Reserve three equal portions of the outer error budget. -/
def Accuracy.triple (k : Accuracy) : Accuracy := ⟨3 * k.val, by have := k.property; omega⟩

@[simp] theorem Accuracy.triple_bound (k : Accuracy) :
    k.triple.bound = k.bound / 3 := by
  simp only [Accuracy.bound, Accuracy.triple, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
  rw [ENNReal.mul_inv (by simp) (by simp), mul_comm]

@[simp] theorem encodeSchemeInput_idxOf_false (x : Word) (k : Accuracy) :
    (encodeSchemeInput x k).idxOf false = k.val := by
  unfold encodeSchemeInput
  rw [List.idxOf_append_of_notMem (by simp)]
  simp

/-- The raw encoded input can be copied by a certified machine. -/
theorem schemeInput_bits_efficient :
    ComputableTidilyInPolyTime (fun a => schemeInputEncoding a) schemeInputEncoding encBits :=
  .of_eq (fun _ => rfl)

/-- Decode the unary accuracy index, rather than treating it as a free parameter. -/
theorem schemeInput_index_efficient :
    ComputableTidilyInPolyTime (fun a : Word × Accuracy => a.2.val)
      schemeInputEncoding encUnary := by
  have h := ComputableTidilyInPolyTime.idxOfWithInput
    (ComputableTidilyInPolyTime.bitsToList.comp schemeInput_bits_efficient)
    (ComputableTidilyInPolyTime.const false)
  exact h.of_enc_eq (fun a => by simp [schemeInputEncoding])

/-- Decode the input word by dropping the unary prefix and its delimiter. -/
theorem schemeInput_word_efficient :
    ComputableTidilyInPolyTime (fun a : Word × Accuracy => a.1)
      schemeInputEncoding encBits := by
  have hcount : ComputableTidilyInPolyTime (fun a : Word × Accuracy => a.2.val + 1)
      schemeInputEncoding encUnary := by
    have h := schemeInput_index_efficient
    fun_prop
  have h := ComputableTidilyInPolyTime.bitsDropWithInput schemeInput_bits_efficient hcount
  exact h.of_enc_eq (fun a => by
    simp [schemeInputEncoding, encodeSchemeInput, List.drop_append, List.drop_replicate])

/-- Construct a new encoded scheme input using a computed positive index. -/
theorem schemeInput_pair_efficient {α : Type} {input : α ↪ Word}
    {word : α → Word} {index : α → Accuracy}
    (hword : ComputableTidilyInPolyTime word input encBits)
    (hindex : ComputableTidilyInPolyTime (fun a => (index a).val) input encUnary) :
    ComputableTidilyInPolyTime (fun a => (word a, index a)) input schemeInputEncoding := by
  have hprefix := (ComputableTidilyInPolyTime.bitsReplicate true).comp hindex
  have hencoded : ComputableTidilyInPolyTime
      (fun a => List.replicate (index a).val true ++ false :: word a) input encBits := by
    fun_prop
  exact hencoded.of_enc_eq (fun _ => rfl)

/-- Accuracy rescaling is polynomial-time on the actual delimited input encoding. -/
theorem tripleInput_efficient :
    ComputableTidilyInPolyTime (fun a : Word × Accuracy => (a.1, a.2.triple))
      schemeInputEncoding schemeInputEncoding := by
  apply schemeInput_pair_efficient schemeInput_word_efficient
  change ComputableTidilyInPolyTime (fun a : Word × Accuracy => 3 * a.2.val)
    schemeInputEncoding encUnary
  have h := schemeInput_index_efficient
  fun_prop

end AverageCaseComplexity
