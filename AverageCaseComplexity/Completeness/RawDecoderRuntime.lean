module

public import AverageCaseComplexity.Completeness.BoundedMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- The machine parser can be viewed as a decoder onto the two descriptions and
symbols that actually determine its execution. -/
def decodeRawFairMachineDescriptions (code : Word) :
    Option (Desc × (Desc × (ℕ × ℕ))) := do
  let machine ← decodeRawFairMachine code
  let falseDesc : Desc := ⟨machine.tapes, machine.initial, machine.falseTable⟩
  let trueDesc : Desc := ⟨machine.tapes, machine.initial, machine.trueTable⟩
  pure (falseDesc, (trueDesc, (machine.falseSymbol, machine.trueSymbol)))

/-- Single-pass state update for unary-delimited fields. The list is kept in
reverse order, as in `decodeRawFieldsAux`. -/
def rawFieldStep (state : ℕ × List ℕ) (bit : Bool) : ℕ × List ℕ :=
  if bit then (state.1 + 1, state.2) else (0, state.1 :: state.2)

def scanRawFields (code : Word) : Option (List ℕ) :=
  let (count, fields) := code.foldl rawFieldStep (0, [])
  if count = 0 then some fields.reverse else none

theorem decodeRawFieldsAux_foldl (code : Word) (count : ℕ) (fields : List ℕ) :
    decodeRawFieldsAux code count fields =
      (let state := code.foldl rawFieldStep (count, fields)
       if state.1 = 0 then some state.2.reverse else none) := by
  induction code generalizing count fields with
  | nil => cases count <;> simp [decodeRawFieldsAux]
  | cons bit code ih =>
      cases bit <;> simp [List.foldl, rawFieldStep, decodeRawFieldsAux, ih]

theorem scanRawFields_eq_decode (code : Word) :
    scanRawFields code = decodeRawFields code := by
  simp [scanRawFields, decodeRawFields, decodeRawFieldsAux_foldl]

private theorem foldl_cons_eq_reverse (values : List ℕ) :
    values.foldl (fun acc value => value :: acc) [] = values.reverse := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.foldl_cons]

/-- Reversing a unary list is polynomial-time: the fold accumulator is just a
permutation of the consumed prefix, so its framed size never exceeds the input. -/
theorem reverseUnaryList_efficient :
    ComputableTidilyInPolyTime (List.reverse : List ℕ → List ℕ)
      (encList encUnary) (encList encUnary) := by
  have hstep : ComputableTidilyInPolyTime
      (fun p : List ℕ × ℕ => p.2 :: p.1)
      (encPair (encList encUnary) encUnary) (encList encUnary) := by
    fun_prop
  have hfold := ComputableTidilyInPolyTime.foldl'
    (list := fun values : List ℕ => values)
    (init := fun _ : List ℕ => [])
    (step := fun acc value => value :: acc)
    (ComputableTidilyInPolyTime.id' (encIn := encList encUnary))
    (ComputableTidilyInPolyTime.const (encIn := encList encUnary) ([] : List ℕ))
    hstep (PolyBounded.self)
    (fun values i hi => by
      have hlen : (encList encUnary ((values.take i).reverse)).length =
          (encList encUnary (values.take i)).length := by
        change (List.flatMap (fun n => frame (encUnary n)) ((values.take i).reverse)).length =
          (List.flatMap (fun n => frame (encUnary n)) (values.take i)).length
        simp [List.length_flatMap, List.map_reverse]
      rw [foldl_cons_eq_reverse, hlen]
      exact length_encList_take_le encUnary values i)
  exact hfold.of_enc_eq (fun values => by
    apply congrArg (encList encUnary)
    exact (foldl_cons_eq_reverse values).symm)

/-- The scan state has polynomially bounded growth; each delimiter transfers its
unary count into the reverse accumulator instead of duplicating it. -/
theorem rawFieldStep_efficient :
    ComputableTidilyInPolyTime (fun p : (ℕ × List ℕ) × Bool =>
      rawFieldStep p.1 p.2)
      (encPair (encPair encUnary (encList encUnary)) encBool)
      (encPair encUnary (encList encUnary)) := by
  unfold rawFieldStep
  fun_prop

theorem rawFieldStep_growth (state : ℕ × List ℕ) (bit : Bool) :
    (encPair encUnary (encList encUnary) (rawFieldStep state bit)).length ≤
      (encPair encUnary (encList encUnary) state).length + 4 := by
  rcases state with ⟨count, fields⟩
  cases bit
  · simp [rawFieldStep, encUnary_apply, List.length_replicate, encList_cons]
  · simp [rawFieldStep, encUnary_apply, List.length_replicate]
    omega

def finishRawFieldScan (state : ℕ × List ℕ) : Option (List ℕ) :=
  if state.1 = 0 then some state.2.reverse else none

theorem finishRawFieldScan_efficient :
    ComputableTidilyInPolyTime finishRawFieldScan
      (encPair encUnary (encList encUnary)) (encOption (encList encUnary)) := by
  have hcount := ComputableTidilyInPolyTime.fst encUnary (encList encUnary)
  have hzero := ComputableTidilyInPolyTime.const
    (encIn := encPair encUnary (encList encUnary)) (encMid := encUnary) 0
  have hguard := hcount.decide_eq' hzero
  have hreverse := reverseUnaryList_efficient.comp
    (ComputableTidilyInPolyTime.snd encUnary (encList encUnary))
  have hsome := (ComputableTidilyInPolyTime.optionSome (encList encUnary)).comp hreverse
  have hnone := ComputableTidilyInPolyTime.const (encIn := encPair encUnary (encList encUnary))
    (encMid := encOption (encList encUnary)) none
  have h := hguard.ite' hsome hnone
  exact h.of_enc_eq (fun state => by simp [finishRawFieldScan])

theorem scanRawFields_efficient :
    ComputableTidilyInPolyTime scanRawFields encBits (encOption (encList encUnary)) := by
  have hscan : ComputableTidilyInPolyTime
      (fun code : Word => code.foldl rawFieldStep (0, [])) encBits
      (encPair encUnary (encList encUnary)) := by
    exact ComputableTidilyInPolyTime.foldl_of_bounded_growth
      (ComputableTidilyInPolyTime.id' (encIn := encBits))
      (ComputableTidilyInPolyTime.const (encIn := encBits) (0, []))
      rawFieldStep_efficient rawFieldStep_growth
  have hfinish := finishRawFieldScan_efficient.comp hscan
  exact hfinish.of_enc_eq (fun code => by simp [scanRawFields, finishRawFieldScan])

/-- The checked raw field decoder itself has an explicit polynomial-time
machine certificate. -/
theorem decodeRawFields_efficient :
    ComputableTidilyInPolyTime decodeRawFields encBits (encOption (encList encUnary)) := by
  have h := scanRawFields_efficient
  exact h.of_enc_eq (fun code => by rw [← scanRawFields_eq_decode])

/-- Read a unary field by its unary index. Missing or malformed input remains
`none`; no partiality is hidden by the accessor. -/
def rawFieldAt (p : Word × ℕ) : Option ℕ :=
  ((decodeRawFields p.1).getD [])[p.2]?

theorem rawFieldAt_efficient :
    ComputableTidilyInPolyTime rawFieldAt (encPair encBits encUnary) (encOption encUnary) := by
  have hfields := decodeRawFields_efficient.comp
    (ComputableTidilyInPolyTime.fst encBits encUnary)
  have hlist := ComputableTidilyInPolyTime.optionGetDWithInput hfields
    (ComputableTidilyInPolyTime.const (encIn := encPair encBits encUnary)
      (encMid := encList encUnary) [])
  have hpair := hlist.prod (ComputableTidilyInPolyTime.snd encBits encUnary)
  have hget : ComputableTidilyInPolyTime
      (fun p : List ℕ × ℕ => p.1[p.2]?)
      (encPair (encList encUnary) encUnary) (encOption encUnary) := by
    fun_prop
  exact hget.comp hpair

def rawTapeField (code : Word) : Option ℕ := rawFieldAt (code, 0)
def rawInitialField (code : Word) : Option ℕ := rawFieldAt (code, 1)
def rawFalseSymbolField (code : Word) : Option ℕ := rawFieldAt (code, 2)
def rawTrueSymbolField (code : Word) : Option ℕ := rawFieldAt (code, 3)
def rawFalseCountField (code : Word) : Option ℕ := rawFieldAt (code, 4)
def rawTrueCountField (code : Word) : Option ℕ := rawFieldAt (code, 5)

theorem rawFieldAt_fixed_efficient (index : ℕ) :
    ComputableTidilyInPolyTime (fun code : Word => rawFieldAt (code, index))
      encBits (encOption encUnary) := by
  have h := rawFieldAt_efficient.comp
    ((ComputableTidilyInPolyTime.id' (encIn := encBits)).prod
      (ComputableTidilyInPolyTime.const (encIn := encBits) (encMid := encUnary) index))
  exact h.of_enc_eq (fun code => rfl)

theorem rawTapeField_efficient :
    ComputableTidilyInPolyTime rawTapeField encBits (encOption encUnary) := by
  exact rawFieldAt_fixed_efficient 0

theorem rawInitialField_efficient :
    ComputableTidilyInPolyTime rawInitialField encBits (encOption encUnary) := by
  exact rawFieldAt_fixed_efficient 1

theorem rawFalseSymbolField_efficient :
    ComputableTidilyInPolyTime rawFalseSymbolField encBits (encOption encUnary) := by
  exact rawFieldAt_fixed_efficient 2

theorem rawTrueSymbolField_efficient :
    ComputableTidilyInPolyTime rawTrueSymbolField encBits (encOption encUnary) := by
  exact rawFieldAt_fixed_efficient 3

theorem rawFalseCountField_efficient :
    ComputableTidilyInPolyTime rawFalseCountField encBits (encOption encUnary) := by
  exact rawFieldAt_fixed_efficient 4

theorem rawTrueCountField_efficient :
    ComputableTidilyInPolyTime rawTrueCountField encBits (encOption encUnary) := by
  exact rawFieldAt_fixed_efficient 5

/-- Boundary examples pin down malformed trailing unary runs and unary field values. -/
example : decodeRawFields [true] = none := by rfl
example : decodeRawFields [true, false, true, true, false] = some [1, 2] := by rfl

end AverageCaseComplexity.Completeness.TwoQuery
