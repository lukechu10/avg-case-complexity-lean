module

public import AverageCaseComplexity.Completeness.FairTableRuntime
public import AverageCaseComplexity.Completeness.ReplayInterface

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery
open Turing.MultiTapeTM Turing.MultiTapeTM.Universal ComputableTidilyInPolyTime

theorem runRaw_efficient_of_structured
    (hs : ComputableTidilyInPolyTime runStructuredTables eStructuredTables (encList encUnary)) :
    ComputableTidilyInPolyTime (fun p : RawFairMachine × Word × Word => runRaw p.1 p.2.1 p.2.2)
      (encPair rawMachineEncoding (encPair encBits encBits)) (encList encUnary) := by
  have hm := fst rawMachineEncoding (encPair encBits encBits)
  have hw := snd rawMachineEncoding (encPair encBits encBits)
  have hd := rawMachineData_efficient.comp hm
  have hx := rawInputSymbols_efficient.comp (hm.prod hw.fst')
  simpa only [runRaw, runTables_structured, Function.comp_def, rawMachineData, eStructuredTables] using
    hs.comp (hd.fst'.prod (hd.snd'.fst'.prod (hx.prod hw.snd')))

/-- Padding after the source (rather than before it) also handles oversize output. -/
theorem normalizeWord_word (n : ℕ) (w : Word) :
    (normalizeWord n w).toWord = (w ++ List.replicate n false).take n := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < n := by simpa using h₁
    by_cases hw : i < w.length
    · simp [FixedWord.toWord, normalizeWord, hw, List.getElem_append_left]
    · simp [FixedWord.toWord, normalizeWord, List.getElem?_eq_none (by omega : w.length ≤ i),
        List.getElem_append_right (by omega : w.length ≤ i)]

theorem normalizeWord_efficient : ComputableTidilyInPolyTime
    (fun p : ℕ × Word => (normalizeWord p.1 p.2).toWord) (encPair encUnary encBits) encBits := by
  simp only [normalizeWord_word]
  fun_prop

private def blankRaw : RawFairMachine := ⟨0,0,0,1,[],[]⟩

/-- Execute the structured interpreter once on the bounded input returned by
compact decoding. Dummy values only totalize projections in the rejected branches. -/
theorem replayAnswer_efficient_of_decoders
    (hs : ComputableTidilyInPolyTime runStructuredTables eStructuredTables (encList encUnary))
    (hd : ComputableTidilyInPolyTime decodeRawFairMachine encBits (encOption rawMachineEncoding))
    (hc : ComputableTidilyInPolyTime (fun p : Word × Word × Word => (decodeSpecializedCode p.1).map
      (fun a => (a.1, boundedSchemeInput p.2.1 a.2 p.2.2.length)))
      (encPair encBits (encPair encBits encBits)) (encOption (encPair encBits encBits))) :
    ComputableTidilyInPolyTime (fun p : Word × Word × Word => replayAnswer p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) answerEncoding := by
  let input := encPair encBits (encPair encBits encBits)
  let ctx := fun p : Word × Word × Word => (decodeSpecializedCode p.1).map
      (fun a => (a.1, boundedSchemeInput p.2.1 a.2 p.2.2.length))
  let fields := fun p => (ctx p).getD ([],[])
  let mach := fun p => decodeRawFairMachine (fields p).1
  let value := fun p => (mach p).getD blankRaw
  have hf : ComputableTidilyInPolyTime fields input (encPair encBits encBits) :=
    optionGetDWithInput hc (.const ([],[]))
  have hm : ComputableTidilyInPolyTime mach input (encOption rawMachineEncoding) := hd.comp hf.fst'
  have hv : ComputableTidilyInPolyTime value input rawMachineEncoding := optionGetDWithInput hm (.const _)
  have hout := (runRaw_efficient_of_structured hs).comp
    (hv.prod (hf.snd'.prod (snd encBits (encPair encBits encBits)).snd'))
  have h := (optionIsSome hc).ite' ((optionIsSome hm).ite'
    (rawAnswer_efficient.comp (hv.prod hout)) (.const none)) (.const none)
  apply h.of_enc_eq
  rintro ⟨code,x,coins⟩
  cases ht : decodeSpecializedCode code with
  | none => simp [replayAnswer, ht]
  | some pair =>
    cases hm : decodeRawFairMachine pair.1 <;>
      simp [replayAnswer, ht, ctx, mach, fields, value, hm]

/-- Compile bounded unary sampler execution, including rejection and normalized output. -/
theorem replaySample_efficient_of_decoder
    (hs : ComputableTidilyInPolyTime runStructuredTables eStructuredTables (encList encUnary))
    (hd : ComputableTidilyInPolyTime decodeRawFairMachine encBits (encOption rawMachineEncoding)) :
    ComputableTidilyInPolyTime (fun p : Word × ℕ × Word => (replaySample p.1 p.2.1 p.2.2).toWord)
      (encPair encBits (encPair encUnary encBits)) encBits := by
  let input := encPair encBits (encPair encUnary encBits)
  let mach := fun p : Word × ℕ × Word => decodeRawFairMachine p.1
  let value := fun p => (mach p).getD blankRaw
  have hm : ComputableTidilyInPolyTime mach input (encOption rawMachineEncoding) :=
    hd.comp (fst encBits (encPair encUnary encBits))
  have hv : ComputableTidilyInPolyTime value input rawMachineEncoding := optionGetDWithInput hm (.const _)
  have par := snd encBits (encPair encUnary encBits)
  have hx : ComputableTidilyInPolyTime (fun p : Word × ℕ × Word => boundedUnaryInput p.2.1 p.2.2.length)
      input encBits := by unfold boundedUnaryInput input; fun_prop
  have hout := (runRaw_efficient_of_structured hs).comp (hv.prod (hx.prod par.snd'))
  have bits := (optionIsSome hm).ite' (outputBits_efficient.comp (hv.prod hout)) (.const [])
  apply (normalizeWord_efficient.comp (par.fst'.prod bits)).of_enc_eq
  rintro ⟨code,n,coins⟩
  cases h : decodeRawFairMachine code <;> simp [replaySample, h, mach, value]

end AverageCaseComplexity.Completeness.TwoQuery
