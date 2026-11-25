module

public import AverageCaseComplexity.Completeness.RawDecoderRuntime
public import AverageCaseComplexity.Completeness.RawRowRuntime
public import AverageCaseComplexity.Completeness.ReplayInterface

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Split exactly the requested number of fixed-width row records. -/
def rawRowChunks (tapes count : ℕ) (fields : List ℕ) : List (List ℕ) :=
  let width := 5 + 3 * tapes
  (List.range count).map fun i => (fields.drop (i * width)).take width

def rawRowChunkAt (input : (ℕ × List ℕ) × ℕ) (i : ℕ) : List ℕ :=
  let width := 5 + 3 * input.1.1
  (input.1.2.drop (i * width)).take width

@[fun_prop] theorem takeUnaryList_efficient :
    ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.1.take p.2)
      (encPair (encList encUnary) encUnary) (encList encUnary) := by
  have hlist := ComputableTidilyInPolyTime.fst (encList encUnary) encUnary
  have hindex := ComputableTidilyInPolyTime.snd (encList encUnary) encUnary
  have hlength := (ComputableTidilyInPolyTime.length encUnary).comp hlist
  have hsub := (ComputableTidilyInPolyTime.unary_sub).comp (hlength.prod hindex)
  have hreverse := reverseUnaryList_efficient.comp hlist
  have hdrop := (ComputableTidilyInPolyTime.dropUnary (encA := encUnary)).comp
    (hreverse.prod hsub)
  exact (reverseUnaryList_efficient.comp hdrop).of_enc_eq (fun p => by
    simp [← List.reverse_take])

theorem rawRowChunkAt_efficient :
    ComputableTidilyInPolyTime (fun p : ((ℕ × List ℕ) × ℕ) × ℕ => rawRowChunkAt p.1 p.2)
      (encPair (encPair (encPair encUnary (encList encUnary)) encUnary) encUnary)
      (encList encUnary) := by
  have hinput : ComputableTidilyInPolyTime (fun p : ((ℕ × List ℕ) × ℕ) × ℕ => p.1)
      (encPair (encPair (encPair encUnary (encList encUnary)) encUnary) encUnary)
      (encPair (encPair encUnary (encList encUnary)) encUnary) := by fun_prop
  have hi : ComputableTidilyInPolyTime (fun p : ((ℕ × List ℕ) × ℕ) × ℕ => p.2)
      (encPair (encPair (encPair encUnary (encList encUnary)) encUnary) encUnary) encUnary := by fun_prop
  have hwidth : ComputableTidilyInPolyTime (fun p : (ℕ × List ℕ) × ℕ => 5 + 3 * p.1.1)
      (encPair (encPair encUnary (encList encUnary)) encUnary) encUnary := by fun_prop
  have hfields : ComputableTidilyInPolyTime (fun p : (ℕ × List ℕ) × ℕ => p.1.2)
      (encPair (encPair encUnary (encList encUnary)) encUnary) (encList encUnary) := by fun_prop
  have hoffset := (ComputableTidilyInPolyTime.unary_mul).comp (hi.prod (hwidth.comp hinput))
  have hdrop := (ComputableTidilyInPolyTime.dropUnary (encA := encUnary)).comp
    ((hfields.comp hinput).prod hoffset)
  have htake := takeUnaryList_efficient.comp (hdrop.prod (hwidth.comp hinput))
  exact htake.of_enc_eq (fun p => rfl)

theorem rawRowChunks_efficient :
    ComputableTidilyInPolyTime (fun p : (ℕ × List ℕ) × ℕ =>
      rawRowChunks p.1.1 p.2 p.1.2)
      (encPair (encPair encUnary (encList encUnary)) encUnary)
      (encList (encList encUnary)) := by
  have hindices : ComputableTidilyInPolyTime (fun p : (ℕ × List ℕ) × ℕ => List.range p.2)
      (encPair (encPair encUnary (encList encUnary)) encUnary) (encList encUnary) := by fun_prop
  have hmap := ComputableTidilyInPolyTime.mapWithInput hindices rawRowChunkAt_efficient
  exact hmap.of_enc_eq (fun p => by simp [rawRowChunks, rawRowChunkAt])

def rawDecodedRows (tapes count : ℕ) (fields : List ℕ) : List (Option (Key × Act)) :=
  (rawRowChunks tapes count fields).map (decodeRawRow tapes)

def rawRowFallback : Key × Act :=
  (⟨0, none, []⟩, ⟨SignType.zero, [], none, none⟩)

def rawRowsFromOptions (rows : List (Option (Key × Act))) : List (Key × Act) :=
  rows.map (fun row => row.getD rawRowFallback)

def rawRowsAllDecoded (rows : List (Option (Key × Act))) : Bool :=
  rows.all Option.isSome

/-- Counted row parser: the number of records comes from the header, and the
suffix is rejected unless its length is exactly count times the fixed row width. -/
def decodeRawRowsCounted (tapes count : ℕ) (fields : List ℕ) :
    Option (List (Key × Act)) :=
  let width := 5 + 3 * tapes
  if fields.length = count * width then
    let decoded := rawDecodedRows tapes count fields
    if rawRowsAllDecoded decoded then some (rawRowsFromOptions decoded) else none
  else none

theorem rawRowsFromOptions_efficient :
    ComputableTidilyInPolyTime rawRowsFromOptions
      (encList (encOption (encPair eKey eAct))) (encList (encPair eKey eAct)) := by
  have hget : ComputableTidilyInPolyTime (fun row : Option (Key × Act) => row.getD rawRowFallback)
      (encOption (encPair eKey eAct)) (encPair eKey eAct) := by
    exact (ComputableTidilyInDegree.getD (enc₁ := encPair eKey eAct) rawRowFallback)
      |>.computableTidilyInPolyTime
  exact (ComputableTidilyInPolyTime.map hget).of_enc_eq (fun _ => rfl)

theorem rawRowsAllDecoded_efficient :
    ComputableTidilyInPolyTime rawRowsAllDecoded
      (encList (encOption (encPair eKey eAct))) encBool := by
  have htest : ComputableTidilyInPolyTime
      (fun p : Unit × Option (Key × Act) => p.2.isSome)
      (encPair encUnit (encOption (encPair eKey eAct))) encBool := by
    exact (ComputableTidilyInPolyTime.optionIsSome
      (ComputableTidilyInPolyTime.snd encUnit (encOption (encPair eKey eAct))))
  have hall := ComputableTidilyInPolyTime.allWith htest
    (ComputableTidilyInPolyTime.const ())
    (ComputableTidilyInPolyTime.id' (encIn := encList (encOption (encPair eKey eAct))))
  exact hall.of_enc_eq (fun rows => rfl)

set_option maxHeartbeats 1000000 in
theorem decodeRawRowsCounted_efficient
    (hrow : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℕ => decodeRawRow p.1 p.2)
      (encPair encUnary (encList encUnary))
      (encOption (encPair eKey eAct))) :
    ComputableTidilyInPolyTime (fun p : (ℕ × List ℕ) × ℕ =>
      decodeRawRowsCounted p.1.1 p.2 p.1.2)
      (encPair (encPair encUnary (encList encUnary)) encUnary)
      (encOption (encList (encPair eKey eAct))) := by
  have hchunks := rawRowChunks_efficient
  have hmap : ComputableTidilyInPolyTime
      (fun p : (ℕ × List ℕ) × ℕ => rawDecodedRows p.1.1 p.2 p.1.2)
      (encPair (encPair encUnary (encList encUnary)) encUnary)
      (encList (encOption (encPair eKey eAct))) := by
    have hmap' : ComputableTidilyInPolyTime
        (fun p : (ℕ × List ℕ) × ℕ => (rawRowChunks p.1.1 p.2 p.1.2).map (decodeRawRow p.1.1))
        (encPair (encPair encUnary (encList encUnary)) encUnary)
        (encList (encOption (encPair eKey eAct))) := by
      apply ComputableTidilyInPolyTime.mapWithInput hchunks
      have hp : ComputableTidilyInPolyTime
          (fun p : ((ℕ × List ℕ) × ℕ) × List ℕ => (p.1.1.1, p.2))
          (encPair (encPair (encPair encUnary (encList encUnary)) encUnary)
            (encList encUnary))
          (encPair encUnary (encList encUnary)) := by fun_prop
      exact hrow.comp hp
    exact hmap'.of_enc_eq (fun p => by simp [rawDecodedRows])
  have hrows := rawRowsFromOptions_efficient.comp hmap
  have hall := rawRowsAllDecoded_efficient.comp hmap
  have hsome := (ComputableTidilyInPolyTime.optionSome (encList (encPair eKey eAct))).comp hrows
  have hnone := ComputableTidilyInPolyTime.const
    (encIn := encPair (encPair encUnary (encList encUnary)) encUnary)
    (encMid := encOption (encList (encPair eKey eAct))) none
  have hvalid := hall.ite' hsome hnone
  have hproduct : ComputableTidilyInPolyTime
      (fun p : (ℕ × List ℕ) × ℕ => p.2 * (5 + 3 * p.1.1))
      (encPair (encPair encUnary (encList encUnary)) encUnary) encUnary := by fun_prop
  have hlength : ComputableTidilyInPolyTime (fun p : (ℕ × List ℕ) × ℕ => p.1.2.length)
      (encPair (encPair encUnary (encList encUnary)) encUnary) encUnary := by fun_prop
  have houter := hlength.decide_eq' hproduct
  have h := houter.ite' hvalid hnone
  apply h.of_enc_eq
  intro p
  simp [decodeRawRowsCounted, rawDecodedRows, rawRowsAllDecoded, rawRowsFromOptions]

def rawHeaderAt (fields : List ℕ) (index : ℕ) : ℕ := fields.getD index 0

theorem rawHeaderAt_efficient :
    ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => rawHeaderAt p.1 p.2)
      (encPair (encList encUnary) encUnary) encUnary := by
  unfold rawHeaderAt
  fun_prop

@[fun_prop] theorem rawHeaderAt_fixed_efficient (index : ℕ) :
    ComputableTidilyInPolyTime (fun fields : List ℕ => rawHeaderAt fields index)
      (encList encUnary) encUnary := by
  exact rawHeaderAt_efficient.comp
    ((ComputableTidilyInPolyTime.id' (encIn := encList encUnary)).prod
      (ComputableTidilyInPolyTime.const (encIn := encList encUnary)
        (encMid := encUnary) index))

def rawCountedInputFromFields (fields : List ℕ) : (ℕ × List ℕ) × ℕ :=
  ((rawHeaderAt fields 0, fields.drop 6), rawHeaderAt fields 4 + rawHeaderAt fields 5)

theorem rawCountedInputFromFields_efficient :
    ComputableTidilyInPolyTime rawCountedInputFromFields (encList encUnary)
      (encPair (encPair encUnary (encList encUnary)) encUnary) := by
  have h0 := rawHeaderAt_fixed_efficient 0
  have h4 := rawHeaderAt_fixed_efficient 4
  have h5 := rawHeaderAt_fixed_efficient 5
  have hfields := ComputableTidilyInPolyTime.id' (encIn := encList encUnary)
  have hdrop := (ComputableTidilyInPolyTime.dropUnary (encA := encUnary)).comp
    (hfields.prod (ComputableTidilyInPolyTime.const (encIn := encList encUnary)
      (encMid := encUnary) 6))
  have hsum := ComputableTidilyInPolyTime.unary_add.comp (h4.prod h5)
  exact (h0.prod hdrop).prod hsum |>.of_enc_eq (fun _ => rfl)

def rawMachineDataFromFieldsRows (p : List ℕ × List (Key × Act)) :
    Desc × (Desc × (ℕ × ℕ)) :=
  let tapes := rawHeaderAt p.1 0
  let initial := rawHeaderAt p.1 1
  let falseSymbol := rawHeaderAt p.1 2
  let trueSymbol := rawHeaderAt p.1 3
  let falseCount := rawHeaderAt p.1 4
  (⟨tapes, initial, p.2.take falseCount⟩,
    (⟨tapes, initial, p.2.drop falseCount⟩, (falseSymbol, trueSymbol)))

private theorem rawFoldlCons_eq_reverse {α} (values : List α) :
    values.foldl (fun acc value => value :: acc) [] = values.reverse := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [List.foldl_cons]

theorem reverseListEncoding_efficient {α : Type} (enc : α ↪ Word) :
    ComputableTidilyInPolyTime (List.reverse : List α → List α)
      (encList enc) (encList enc) := by
  have hstep : ComputableTidilyInPolyTime
      (fun p : List α × α => p.2 :: p.1)
      (encPair (encList enc) enc) (encList enc) := by
    exact ComputableTidilyInPolyTime.cons'
      (encIn := encPair (encList enc) enc) (encA := enc)
      (ComputableTidilyInPolyTime.snd (encList enc) enc)
      (ComputableTidilyInPolyTime.fst (encList enc) enc)
  have hfold := ComputableTidilyInPolyTime.foldl'
    (encIn := encList enc) (encA := enc) (encB := encList enc) (encL := encList enc)
    (list := fun values : List α => values)
    (init := fun _ : List α => [])
    (step := fun acc value => value :: acc)
    (ComputableTidilyInPolyTime.id' (encIn := encList enc))
    (ComputableTidilyInPolyTime.const (encIn := encList enc) ([] : List α))
    hstep (PolyBounded.self)
    (fun values i hi => by
      have hlen : (encList enc ((values.take i).reverse)).length =
          (encList enc (values.take i)).length := by
        change (List.flatMap (fun x => frame (enc x)) ((values.take i).reverse)).length =
          (List.flatMap (fun x => frame (enc x)) (values.take i)).length
        simp [List.length_flatMap, List.map_reverse]
      rw [rawFoldlCons_eq_reverse, hlen]
      exact length_encList_take_le enc values i)
  exact hfold.of_enc_eq (fun values => by
    apply congrArg (encList enc)
    exact (rawFoldlCons_eq_reverse values).symm)

theorem takeListEncoding_efficient {α} (enc : α ↪ Word) :
    ComputableTidilyInPolyTime (fun p : List α × ℕ => p.1.take p.2)
      (encPair (encList enc) encUnary) (encList enc) := by
  have hlist := ComputableTidilyInPolyTime.fst (encList enc) encUnary
  have hindex := ComputableTidilyInPolyTime.snd (encList enc) encUnary
  have hlength := (ComputableTidilyInPolyTime.length enc).comp hlist
  have hsub := (ComputableTidilyInPolyTime.unary_sub).comp (hlength.prod hindex)
  have hreverse := reverseListEncoding_efficient enc |>.comp hlist
  have hdrop := (ComputableTidilyInPolyTime.dropUnary (encA := enc)).comp
    (hreverse.prod hsub)
  exact (reverseListEncoding_efficient enc |>.comp hdrop).of_enc_eq (fun p => by
    simp [← List.reverse_take])

theorem rawMachineDataFromFieldsRows_efficient :
    ComputableTidilyInPolyTime rawMachineDataFromFieldsRows
      (encPair (encList encUnary) (encList (encPair eKey eAct)))
      (encPair eDesc (encPair eDesc (encPair encUnary encUnary))) := by
  let eDescFields := encPair encUnary (encPair encUnary (encList (encPair eKey eAct)))
  have hdesc : ComputableTidilyInPolyTime
      (fun p : ℕ × (ℕ × List (Key × Act)) => ⟨p.1, p.2.1, p.2.2⟩)
      eDescFields eDesc := by
    exact (ComputableTidilyInPolyTime.id' (encIn := eDescFields)).of_enc_eq
      (fun p => by simp [eDesc_apply, eDescFields])
  have hfields := ComputableTidilyInPolyTime.fst (encList encUnary)
    (encList (encPair eKey eAct))
  have htable := ComputableTidilyInPolyTime.snd (encList encUnary)
    (encList (encPair eKey eAct))
  have htapes := (rawHeaderAt_fixed_efficient 0).comp hfields
  have hinitial := (rawHeaderAt_fixed_efficient 1).comp hfields
  have hfalseCount := (rawHeaderAt_fixed_efficient 4).comp hfields
  have htake := takeListEncoding_efficient (encPair eKey eAct) |>.comp
    (htable.prod hfalseCount)
  have hdrop := (ComputableTidilyInPolyTime.dropUnary (encA := encPair eKey eAct)).comp
    (htable.prod hfalseCount)
  have hfalseTuple := htapes.prod (hinitial.prod htake)
  have htrueTuple := htapes.prod (hinitial.prod hdrop)
  have hfalseDesc := hdesc.comp hfalseTuple
  have htrueDesc := hdesc.comp htrueTuple
  have hfalseSymbol := (rawHeaderAt_fixed_efficient 2).comp hfields
  have htrueSymbol := (rawHeaderAt_fixed_efficient 3).comp hfields
  have hsymbols := hfalseSymbol.prod htrueSymbol
  exact (hfalseDesc.prod (htrueDesc.prod hsymbols)).of_enc_eq
    (fun p => rfl)

def rawMachineFromFieldsRows (p : List ℕ × List (Key × Act)) : RawFairMachine :=
  ⟨rawHeaderAt p.1 0, rawHeaderAt p.1 1, rawHeaderAt p.1 2, rawHeaderAt p.1 3,
    p.2.take (rawHeaderAt p.1 4), p.2.drop (rawHeaderAt p.1 4)⟩

theorem rawMachineFromFieldsRows_efficient :
    ComputableTidilyInPolyTime rawMachineFromFieldsRows
      (encPair (encList encUnary) (encList (encPair eKey eAct))) rawMachineEncoding := by
  exact rawMachineDataFromFieldsRows_efficient.of_enc_eq (fun p => by
    simp [rawMachineEncoding_apply, rawMachineData, rawMachineFromFieldsRows,
      rawMachineDataFromFieldsRows, eDesc_apply])

def decodeRawFairMachineFieldsRuntime (fields : List ℕ) : Option RawFairMachine := do
  if fields.length < 6 then none else
  let falseSymbol := rawHeaderAt fields 2
  let trueSymbol := rawHeaderAt fields 3
  if falseSymbol = trueSymbol then none else
  let input := rawCountedInputFromFields fields
  let rows ← decodeRawRowsCounted input.1.1 input.2 input.1.2
  if rows.length = input.2 then
    some (rawMachineFromFieldsRows (fields, rows))
  else none

theorem decodeRawFairMachineFieldsRuntime_efficient
    (hrow : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℕ => decodeRawRow p.1 p.2)
      (encPair encUnary (encList encUnary))
      (encOption (encPair eKey eAct))) :
    ComputableTidilyInPolyTime decodeRawFairMachineFieldsRuntime
      (encList encUnary) (encOption rawMachineEncoding) := by
  have hcounted := decodeRawRowsCounted_efficient hrow
  have hinput := rawCountedInputFromFields_efficient
  have hrows : ComputableTidilyInPolyTime
      (fun fields : List ℕ => decodeRawRowsCounted
        (rawCountedInputFromFields fields).1.1
        (rawCountedInputFromFields fields).2
        (rawCountedInputFromFields fields).1.2)
      (encList encUnary) (encOption (encList (encPair eKey eAct))) :=
    hcounted.comp hinput
  have hassemble : ComputableTidilyInPolyTime
      (fun p : List ℕ × List (Key × Act) => rawMachineFromFieldsRows p)
      (encPair (encList encUnary) (encList (encPair eKey eAct))) rawMachineEncoding :=
    rawMachineFromFieldsRows_efficient
  have hrowsGet := ComputableTidilyInPolyTime.optionGetDWithInput hrows
    (ComputableTidilyInPolyTime.const
      (encIn := encList encUnary) (encMid := encList (encPair eKey eAct)) [])
  have hpair := (ComputableTidilyInPolyTime.id' (encIn := encList encUnary)).prod hrowsGet
  have hassembled := hassemble.comp hpair
  have hsome := (ComputableTidilyInPolyTime.optionSome rawMachineEncoding).comp hassembled
  have hnone := ComputableTidilyInPolyTime.const (encIn := encList encUnary)
    (encMid := encOption rawMachineEncoding) none
  have hshort : ComputableTidilyInPolyTime (fun fields : List ℕ => decide (6 ≤ fields.length))
      (encList encUnary) encBool := by fun_prop
  have hrowsSome := ComputableTidilyInPolyTime.optionIsSome hrows
  have hrowsLength := (ComputableTidilyInPolyTime.length (encPair eKey eAct)).comp hrowsGet
  have hcount := (ComputableTidilyInPolyTime.snd (encPair encUnary (encList encUnary)) encUnary).comp hinput
  have hrowCount := hrowsLength.decide_eq' hcount
  have hvalidRows := (ComputableTidilyInPolyTime.bool_and.comp (hrowsSome.prod hrowCount))
  have hfalseSymbol := rawHeaderAt_fixed_efficient 2
  have htrueSymbol := rawHeaderAt_fixed_efficient 3
  have hsymbols := hfalseSymbol.prod htrueSymbol
  have hdifferent := ComputableTidilyInPolyTime.bool_not.comp
    (hfalseSymbol.decide_eq' htrueSymbol)
  have hbody := (ComputableTidilyInPolyTime.bool_and.comp (hdifferent.prod hvalidRows))
  have hgood := (ComputableTidilyInPolyTime.bool_and.comp (hshort.prod hbody))
  have h := hgood.ite' hsome hnone
  apply h.of_enc_eq
  intro fields
  by_cases hshort' : fields.length < 6
  · have hnotlong : ¬ 6 ≤ fields.length := by omega
    simp [decodeRawFairMachineFieldsRuntime, rawCountedInputFromFields,
      hshort', hnotlong]
  · have hlong' : 6 ≤ fields.length := by omega
    by_cases hsym' : rawHeaderAt fields 2 = rawHeaderAt fields 3
    · simp [decodeRawFairMachineFieldsRuntime, rawCountedInputFromFields,
        hshort', hlong', hsym']
    · cases hrows' : decodeRawRowsCounted (rawHeaderAt fields 0)
          (rawHeaderAt fields 4 + rawHeaderAt fields 5) (fields.drop 6) with
      | none =>
          simp [decodeRawFairMachineFieldsRuntime, rawCountedInputFromFields,
            rawMachineFromFieldsRows, hshort', hlong', hsym', hrows']
      | some rows =>
          by_cases hcount' : rows.length = rawHeaderAt fields 4 + rawHeaderAt fields 5
          · simp [decodeRawFairMachineFieldsRuntime, rawCountedInputFromFields,
              rawMachineFromFieldsRows, hshort', hlong', hsym', hrows', hcount']
          · simp [decodeRawFairMachineFieldsRuntime, rawCountedInputFromFields,
              rawMachineFromFieldsRows, hshort', hlong', hsym', hrows', hcount']

def decodeRawFairMachineRuntime (code : Word) : Option RawFairMachine :=
  decodeRawFairMachineFieldsRuntime ((decodeRawFields code).getD [])

theorem decodeRawFairMachineRuntime_efficient
    (hrow : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℕ => decodeRawRow p.1 p.2)
      (encPair encUnary (encList encUnary))
      (encOption (encPair eKey eAct))) :
    ComputableTidilyInPolyTime decodeRawFairMachineRuntime encBits
      (encOption rawMachineEncoding) := by
  have hfields := ComputableTidilyInPolyTime.optionGetDWithInput decodeRawFields_efficient
    (ComputableTidilyInPolyTime.const (encIn := encBits)
      (encMid := encList encUnary) [])
  exact (decodeRawFairMachineFieldsRuntime_efficient hrow).comp hfields

theorem rawMachineFalseDesc_efficient :
    ComputableTidilyInPolyTime
      (fun machine : RawFairMachine =>
        ⟨machine.tapes, machine.initial, machine.falseTable⟩)
      rawMachineEncoding eDesc := by
  exact rawMachineData_efficient.fst'

theorem rawMachineTrueDesc_efficient :
    ComputableTidilyInPolyTime
      (fun machine : RawFairMachine =>
        ⟨machine.tapes, machine.initial, machine.trueTable⟩)
      rawMachineEncoding eDesc := by
  exact rawMachineData_efficient.snd'.fst'

/-- `all` over the decoded row options is exactly the per-chunk validity test. -/
theorem rawRowsAllDecoded_iff_chunks (tapes count : ℕ) (fields : List ℕ) :
    rawRowsAllDecoded (rawDecodedRows tapes count fields) = true ↔
      ∀ chunk ∈ rawRowChunks tapes count fields,
        (decodeRawRow tapes chunk).isSome = true := by
  simp [rawRowsAllDecoded, rawDecodedRows, List.all_eq_true]

/-- Splitting one more row prepends the first fixed-width chunk. -/
theorem rawRowChunks_succ (tapes count : ℕ) (fields : List ℕ) :
    rawRowChunks tapes (count + 1) fields =
      rawRowChunkAt ((tapes, fields), 0) 0 ::
        rawRowChunks tapes count (fields.drop (5 + 3 * tapes)) := by
  simp [rawRowChunks, rawRowChunkAt, List.range_succ_eq_map, List.map_map,
    List.drop_drop, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A successful fixed-fuel parser consumes exactly the requested number of
fixed-width fields. -/
theorem decodeRawRowsAux_success_length (tapes count : ℕ) (fields : List ℕ)
    {rows : List (Key × Act)}
    (h : decodeRawRowsAux tapes count fields = some rows) :
    fields.length = count * (5 + 3 * tapes) := by
  induction count generalizing fields rows with
  | zero => cases fields <;> simp [decodeRawRowsAux] at h <;> simp_all
  | succ count ih =>
      simp only [decodeRawRowsAux, Bind.bind, Option.bind_eq_some_iff] at h
      rcases h with ⟨⟨rowFields, rest⟩, htake, hrest⟩
      rcases hrest with ⟨row, hrow, hrest⟩
      rcases hrest with ⟨tail, haux, hresult⟩
      have hlen := ih (fields := rest) (rows := tail) haux
      have hsplit : fields.length = (5 + 3 * tapes) + rest.length := by
        have := takeRawFields_length_relation htake
        omega
      rw [Nat.succ_mul]
      omega

theorem decodeRawRowsAux_success_rows_length (tapes count : ℕ) (fields : List ℕ)
    {rows : List (Key × Act)}
    (h : decodeRawRowsAux tapes count fields = some rows) : rows.length = count := by
  induction count generalizing fields rows with
  | zero => cases fields <;> simp [decodeRawRowsAux] at h ⊢ <;> simp_all
  | succ count ih =>
      simp only [decodeRawRowsAux, Bind.bind, Option.bind_eq_some_iff] at h
      rcases h with ⟨⟨rowFields, rest⟩, htake, hrest⟩
      rcases hrest with ⟨row, hrow, hrest⟩
      rcases hrest with ⟨tail, haux, hresult⟩
      have hrows : rows = row :: tail := by simpa using hresult.symm
      have htailLen := ih (fields := rest) haux
      simp [hrows, htailLen]

/-- The counted row parser agrees with the legacy parser followed by an
explicit check that its parsed row count matches the header. -/
theorem decodeRawRowsCounted_eq_decodeRawRows_check
    (tapes count : ℕ) (fields : List ℕ) :
    decodeRawRowsCounted tapes count fields =
      (decodeRawRows tapes fields).bind (fun rows =>
        if rows.length = count then some rows else none) := by
  have hw : 0 < 5 + 3 * tapes := by omega
  by_cases hwidth : fields.length = count * (5 + 3 * tapes)
  · have hdiv : fields.length / (5 + 3 * tapes) = count := by
      rw [hwidth, Nat.mul_comm]
      exact Nat.mul_div_right count hw
    have hchunks : decodeRawRowsAux tapes count fields =
        if rawRowsAllDecoded (rawDecodedRows tapes count fields) then
          some (rawRowsFromOptions (rawDecodedRows tapes count fields)) else none := by
      induction count generalizing fields with
      | zero =>
          have hnil : fields = [] := by
            have : fields.length = 0 := by simpa using hwidth
            cases fields with
            | nil => rfl
            | cons x xs => simp at this
          subst fields
          simp [rawDecodedRows, rawRowChunks, rawRowsAllDecoded, rawRowsFromOptions,
            decodeRawRowsAux]
      | succ count ih =>
          have hlenDrop : (fields.drop (5 + 3 * tapes)).length = count * (5 + 3 * tapes) := by
            rw [List.length_drop]
            rw [Nat.succ_mul] at hwidth
            rw [hwidth, Nat.add_sub_cancel_right]
          have htake : takeRawFields (5 + 3 * tapes) fields =
              some (fields.take (5 + 3 * tapes), fields.drop (5 + 3 * tapes)) := by
            rw [takeRawFields_eq_take_drop]
            have : 5 + 3 * tapes ≤ fields.length := by
              simp only [Nat.succ_mul] at hwidth
              omega
            simp [this]
          have htaildiv : (fields.drop (5 + 3 * tapes)).length / (5 + 3 * tapes) = count := by
            rw [hlenDrop, Nat.mul_comm]
            exact Nat.mul_div_right count hw
          have htail := ih (fields := fields.drop (5 + 3 * tapes)) hlenDrop htaildiv
          simp only [rawDecodedRows, rawRowChunks_succ, rawRowChunkAt,
            Nat.zero_mul, List.drop_zero]
          simp only [decodeRawRowsAux, Bind.bind, htake, Option.bind_some]
          cases hfirst : decodeRawRow tapes (fields.take (5 + 3 * tapes)) with
          | none => simp [hfirst, htail, rawRowsAllDecoded, rawRowsFromOptions, rawDecodedRows]
          | some row =>
              by_cases hgood : ∀ x ∈ rawRowChunks tapes count (fields.drop (5 + 3 * tapes)),
                  (decodeRawRow tapes x).isSome = true
              · have hgoodTail : rawRowsAllDecoded
                    (rawDecodedRows tapes count (fields.drop (5 + 3 * tapes))) = true :=
                    (rawRowsAllDecoded_iff_chunks tapes count
                      (fields.drop (5 + 3 * tapes))).2 hgood
                have htail' : decodeRawRowsAux tapes count (fields.drop (5 + 3 * tapes)) =
                    some (rawRowsFromOptions (rawDecodedRows tapes count (fields.drop (5 + 3 * tapes)))) := by
                  rw [htail]
                  simp [hgoodTail]
                have hgoodFull : rawRowsAllDecoded
                    (rawDecodedRows tapes (count + 1) fields) = true := by
                  apply (rawRowsAllDecoded_iff_chunks tapes (count + 1) fields).2
                  intro chunk hmem
                  rw [rawRowChunks_succ] at hmem
                  simp only [List.mem_cons] at hmem
                  rcases hmem with hhead | htailmem
                  · subst chunk
                    simp [rawRowChunkAt, hfirst]
                  · exact hgood chunk htailmem
                rw [htail']
                have hgoodList : rawRowsAllDecoded
                    (some row :: List.map (decodeRawRow tapes)
                      (rawRowChunks tapes count (fields.drop (5 + 3 * tapes)))) = true := by
                  simpa [rawDecodedRows, rawRowChunks_succ, rawRowChunkAt, hfirst] using hgoodFull
                simp [hfirst, hgoodList, rawRowsFromOptions, rawDecodedRows]
              · have hbadTail : rawRowsAllDecoded
                    (rawDecodedRows tapes count (fields.drop (5 + 3 * tapes))) = false := by
                  cases h : rawRowsAllDecoded
                      (rawDecodedRows tapes count (fields.drop (5 + 3 * tapes))) with
                  | false => rfl
                  | true =>
                      have hvalid := (rawRowsAllDecoded_iff_chunks tapes count
                        (fields.drop (5 + 3 * tapes))).1 h
                      exact False.elim (hgood hvalid)
                have hfullNot : ¬ ∀ chunk ∈ rawRowChunks tapes (count + 1) fields,
                    (decodeRawRow tapes chunk).isSome = true := by
                  intro hfull
                  rw [rawRowChunks_succ] at hfull
                  apply hgood
                  intro chunk hmem
                  exact hfull chunk (by simp [hmem])
                have hbadFull : rawRowsAllDecoded
                    (rawDecodedRows tapes (count + 1) fields) = false := by
                  cases h : rawRowsAllDecoded (rawDecodedRows tapes (count + 1) fields) with
                  | false => rfl
                  | true =>
                      have hvalid := (rawRowsAllDecoded_iff_chunks tapes (count + 1) fields).1 h
                      exact False.elim (hfullNot hvalid)
                have hbadList : rawRowsAllDecoded
                    (some row :: List.map (decodeRawRow tapes)
                      (rawRowChunks tapes count (fields.drop (5 + 3 * tapes)))) = false := by
                  simpa [rawDecodedRows, rawRowChunks_succ, rawRowChunkAt, hfirst] using hbadFull
                rw [htail]
                simp [hfirst, hgood, hbadList, rawRowsFromOptions]
                simpa [rawDecodedRows] using hbadTail
    have hdecode : decodeRawRows tapes fields = decodeRawRowsAux tapes count fields := by
      simp [decodeRawRows, hdiv]
    rw [hdecode]
    have hlenRows : (rawRowsFromOptions (rawDecodedRows tapes count fields)).length = count := by
      simp [rawRowsFromOptions, rawDecodedRows, rawRowChunks]
    by_cases hgood : rawRowsAllDecoded (rawDecodedRows tapes count fields) = true
    · simp [decodeRawRowsCounted, hwidth, hchunks, hgood, hlenRows]
    · have hnotgood : rawRowsAllDecoded (rawDecodedRows tapes count fields) = false := by
        cases h : rawRowsAllDecoded (rawDecodedRows tapes count fields) <;> simp_all
      simp [decodeRawRowsCounted, hwidth, hchunks, hnotgood]
  · cases hrows : decodeRawRows tapes fields with
    | none => simp [decodeRawRowsCounted, hwidth, hrows]
    | some rows =>
        have hsuccess : decodeRawRowsAux tapes (fields.length / (5 + 3 * tapes)) fields = some rows := by
          simpa [decodeRawRows] using hrows
        have hrowsLen := decodeRawRowsAux_success_rows_length tapes _ fields hsuccess
        have hfieldsLen := decodeRawRowsAux_success_length tapes _ fields hsuccess
        by_cases hcount : rows.length = count
        · have hfieldsCount : fields.length = count * (5 + 3 * tapes) := by
            rw [← hrowsLen, hcount] at hfieldsLen
            exact hfieldsLen
          exact False.elim (hwidth hfieldsCount)
        · simp [decodeRawRowsCounted, hwidth, hrows, hcount]

/-- The counted parser is the only semantic correspondence premise needed to
transfer the runtime-oriented header assembly back to the existing decoder. -/
theorem decodeRawFairMachineRuntime_eq
    (hcounted : ∀ (tapes count : ℕ) (fields : List ℕ),
      decodeRawRowsCounted tapes count fields =
        (decodeRawRows tapes fields).bind (fun rows =>
          if rows.length = count then some rows else none))
    (code : Word) :
    decodeRawFairMachineRuntime code = decodeRawFairMachine code := by
  unfold decodeRawFairMachineRuntime
  cases hfields : decodeRawFields code with
  | none => simp [decodeRawFairMachine, decodeRawFairMachineFieldsRuntime, hfields]
  | some fields =>
      cases fields with
      | nil => simp [decodeRawFairMachine, hfields, decodeRawFairMachineFieldsRuntime]
      | cons tapes rest =>
          cases rest with
          | nil => simp [decodeRawFairMachine, hfields, decodeRawFairMachineFieldsRuntime]
          | cons initial rest =>
              cases rest with
              | nil => simp [decodeRawFairMachine, hfields, decodeRawFairMachineFieldsRuntime]
              | cons falseSymbol rest =>
                  cases rest with
                  | nil => simp [decodeRawFairMachine, hfields, decodeRawFairMachineFieldsRuntime]
                  | cons trueSymbol rest =>
                      cases rest with
                      | nil => simp [decodeRawFairMachine, hfields, decodeRawFairMachineFieldsRuntime]
                      | cons falseCount rest =>
                          cases rest with
                          | nil => simp [decodeRawFairMachine, hfields, decodeRawFairMachineFieldsRuntime]
                          | cons trueCount rowFields =>
                              have hrows := hcounted tapes (falseCount + trueCount) rowFields
                              have hlenFields : 6 ≤
                                  (tapes :: initial :: falseSymbol :: trueSymbol :: falseCount :: trueCount :: rowFields).length := by
                                simp
                              have hnotshort : ¬ rowFields.length + 1 + 1 + 1 + 1 + 1 + 1 < 6 := by
                                simp only [List.length_cons] at hlenFields
                                omega
                              by_cases hsym : falseSymbol = trueSymbol
                              · simp [decodeRawFairMachine, hfields, decodeRawFairMachineFieldsRuntime,
                                  rawCountedInputFromFields, rawMachineFromFieldsRows,
                                  rawHeaderAt, hrows, hnotshort, hsym]
                              · cases hdecoded : decodeRawRows tapes rowFields with
                                | none =>
                                    simp [decodeRawFairMachine, hfields, decodeRawFairMachineFieldsRuntime,
                                      rawCountedInputFromFields, rawMachineFromFieldsRows,
                                      rawHeaderAt, hrows, hnotshort, hsym, hdecoded]
                                | some rows =>
                                    by_cases hcount : rows.length = falseCount + trueCount
                                    · simp [decodeRawFairMachine, hfields, decodeRawFairMachineFieldsRuntime,
                                        rawCountedInputFromFields, rawMachineFromFieldsRows,
                                        rawHeaderAt, hrows, hnotshort, hsym, hdecoded, hcount]
                                    · simp [decodeRawFairMachine, hfields, decodeRawFairMachineFieldsRuntime,
                                        rawCountedInputFromFields, rawMachineFromFieldsRows,
                                        rawHeaderAt, hrows, hnotshort, hsym, hdecoded, hcount]

theorem decodeRawFairMachine_efficient
    (hrow : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℕ => decodeRawRow p.1 p.2)
      (encPair encUnary (encList encUnary))
      (encOption (encPair eKey eAct))) :
    ComputableTidilyInPolyTime decodeRawFairMachine encBits
      (encOption rawMachineEncoding) := by
  exact (decodeRawFairMachineRuntime_efficient hrow).of_enc_eq
    (fun code => by rw [decodeRawFairMachineRuntime_eq decodeRawRowsCounted_eq_decodeRawRows_check code])

end AverageCaseComplexity.Completeness.TwoQuery
