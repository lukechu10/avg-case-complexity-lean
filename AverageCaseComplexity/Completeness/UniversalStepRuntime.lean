module

public import AverageCaseComplexity.Completeness.TupleDecodingRuntime
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Compose

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal Cslib.BitString

/-- The head is stored in binary. On arbitrary configurations it can be exponentially
far beyond the input; saturate the index before converting it to unary for lookup. -/
theorem inputSymbol_efficient : ComputableTidilyInPolyTime
    (fun p : List ℕ × ℕ => inputSymbol p.1 p.2) (encPair (encList encUnary) encNat) eSym := by
  let enc := encPair (encList encUnary) encNat
  let sat := fun p : List ℕ × ℕ => boundedBinaryValue (p.1.length+1) p.2.bits.reverse
  have hx : ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.1) enc (encList encUnary) := .fst ..
  have hp : ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.2.bits) enc encBits :=
    (ComputableTidilyInPolyTime.snd (encList encUnary) encNat).of_enc_eq (fun _ => rfl)
  have hs : ComputableTidilyInPolyTime sat enc encUnary := by unfold sat; fun_prop
  have hs_eq (p : List ℕ × ℕ) : sat p = min (p.1.length+1) p.2 := by
    simp [sat, boundedBinaryValue_eq, ← foldr_bit_eq_binaryValue_reverse]
  have h : ComputableTidilyInPolyTime (fun p : List ℕ × ℕ =>
      if sat p = 0 then none else p.1[sat p - 1]?) enc eSym := by
    apply ComputableTidilyInPolyTime.ite_decide (hs.decide_eq' (.const 0)) (.const none)
    exact ComputableTidilyInPolyTime.getElem? hx
      (ComputableTidilyInPolyTime.unary_sub.comp (hs.prod (.const 1)))
  apply h.of_enc_eq
  intro p
  simp only [inputSymbol, hs_eq, List.head?_drop]
  by_cases hle : p.2 ≤ p.1.length + 1
  · rw [min_eq_right hle]
  · rw [min_eq_left (by omega)]
    simp [show p.2 ≠ 0 by omega, List.getElem?_eq_none (by omega : p.1.length ≤ p.2-1)]

/-- A tidy polynomial-time step even on an unreachable configuration. -/
theorem universalStep_efficient : ComputableTidilyInPolyTime
    (fun c : Ctx => step c.1.1 c.1.2 c.2) eCtx (encPair eCfg eSym) := by
  have base := stepWith_inO.computableTidilyInPolyTime ⟨2,3,wTime_le'⟩ ⟨1,1,fun _ => by simp⟩
  have cfg := ComputableTidilyInPolyTime.snd (encPair eDesc (encList encUnary)) eCfg
  have par := ComputableTidilyInPolyTime.fst (encPair eDesc (encList encUnary)) eCfg
  have fields : ComputableTidilyInPolyTime (fun c : Ctx => (c.2.state, c.2.inputPos, c.2.workTapes))
      eCtx eCfgFields := cfg.of_enc_eq (fun _ => rfl)
  have sym := inputSymbol_efficient.comp (par.snd'.prod fields.snd'.fst')
  exact (base.comp ((par.fst'.prod cfg).prod sym)).of_enc_eq (fun c => by
    rw [step_eq_stepWith]; rfl)

end AverageCaseComplexity.Completeness.TwoQuery
