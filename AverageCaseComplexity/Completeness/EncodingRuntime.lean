module

public import AverageCaseComplexity.Completeness.TupleEncoding
public import AverageCaseComplexity.Reductions.Accuracy

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM Cslib.Kolmogorov

/-- Construct the logarithmic length header using a certified unary-to-binary
conversion, not an asserted constant-cost conversion of a natural number. -/
@[fun_prop] theorem selfDelimitingCode_efficient :
    ComputableTidilyInPolyTime selfDelimitingCode encBits encBits := by
  have hlength := ComputableTidilyInPolyTime.encoding_length encBits
  have hbinary : ComputableTidilyInPolyTime (fun w : Word => w.length.bits) encBits encBits :=
    (ComputableTidilyInPolyTime.unary_to_binary.comp hlength).of_enc_eq
      (fun w => by simp [encNat_apply])
  have hsize : ComputableTidilyInPolyTime (fun w : Word => w.length.size) encBits encUnary := by
    have h := (ComputableTidilyInPolyTime.encoding_length encBits).comp hbinary
    exact h.of_enc_eq (fun w => by simp [Function.comp_apply, encBits, Nat.size_eq_bits_len])
  have hprefix := (ComputableTidilyInPolyTime.bitsReplicate true).comp hsize
  have hword : ComputableTidilyInPolyTime (fun w : Word => w) encBits encBits := .id'
  have hzero : ComputableTidilyInPolyTime (fun _ : Word => false) encBits encBool := .const false
  exact hprefix.bitsAppend (hzero.bitsCons (hbinary.bitsAppend hword))

/-- Assemble an external seed encoding from independently certified field
constructors. Only the external representation has logarithmic overhead;
internal machine plumbing may use the library's standard encodings. -/
theorem encodeSeed_efficient_with {α : Type} {input : α ↪ Word} {seed : α → Seed}
    (hM : ComputableTidilyInPolyTime (fun a => (seed a).machineCode) input encBits)
    (hx : ComputableTidilyInPolyTime (fun a => (seed a).input) input encBits)
    (hr : ComputableTidilyInPolyTime (fun a => (seed a).clockBits) input encBits)
    (hb : ComputableTidilyInPolyTime (fun a => (seed a).fallback) input encBool)
    (hS : ComputableTidilyInPolyTime (fun a => (seed a).samplerCode) input encBits)
    (hs : ComputableTidilyInPolyTime (fun a => (seed a).samplerClockBits) input encBits) :
    ComputableTidilyInPolyTime (fun a => encodeSeed (seed a)) input encBits := by
  have hM' := selfDelimitingCode_efficient.comp hM
  have hx' := selfDelimitingCode_efficient.comp hx
  have hr' := selfDelimitingCode_efficient.comp hr
  have hS' := selfDelimitingCode_efficient.comp hS
  have hbit : ComputableTidilyInPolyTime (fun a => [(seed a).fallback]) input encBits :=
    hb.bitsCons (ComputableTidilyInPolyTime.const [])
  exact (hM'.bitsAppend (hx'.bitsAppend (hr'.bitsAppend
    (hbit.bitsAppend (hS'.bitsAppend hs))))).of_enc_eq
      (fun a => by simp [encodeSeed, Function.comp_apply, List.append_assoc])

end AverageCaseComplexity.Completeness.TwoQuery
