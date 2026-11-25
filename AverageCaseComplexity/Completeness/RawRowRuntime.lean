module

public import AverageCaseComplexity.Completeness.RawDecoderRuntime
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Read a field with a fixed default.  The default is observable only on malformed
rows; the enclosing decoder checks the exact row width before using these values. -/
def rawRowField (fields : List ℕ) (index : ℕ) : ℕ := fields[index]?.getD 0

/-- The work-symbol codes in a row, read by indexing the input tape fields. -/
def rawRowWorkCodes (tapes : ℕ) (fields : List ℕ) : List ℕ :=
  (List.range tapes).map fun i => rawRowField fields (2 + i)

/-- The write-symbol codes in a row, read by indexing the action fields. -/
def rawRowWriteCodes (tapes : ℕ) (fields : List ℕ) : List ℕ :=
  (List.range tapes).map fun i => rawRowField fields (3 + tapes + i)

/-- Pair each indexed write with its corresponding indexed movement code. -/
def rawRowTapeActions (tapes : ℕ) (fields : List ℕ) : List TapeAct :=
  (List.range tapes).map fun i =>
    (decodeWriteSymbol (rawRowField fields (3 + tapes + i)),
      decodeMove (rawRowField fields (3 + 2 * tapes + i)))

/-- The work-tape move codes in a row, read by indexing the action fields. -/
def rawRowWorkMoveCodes (tapes : ℕ) (fields : List ℕ) : List ℕ :=
  (List.range tapes).map fun i => rawRowField fields (3 + 2 * tapes + i)

/-- Check the input-tape move and every work-tape move by indexed access. -/
def rawRowMoveValid (move : ℕ) : Bool := validMove move

def rawRowMovesValid (tapes : ℕ) (fields : List ℕ) : Bool :=
  rawRowMoveValid (rawRowField fields (2 + tapes)) &&
    (rawRowWorkMoveCodes tapes fields).all rawRowMoveValid

/-- Total, indexed candidate construction for a raw transition row. -/
def rawRowKeyFields (tapes : ℕ) (fields : List ℕ) :
    ℕ × (Option ℕ × List (Option ℕ)) :=
  (rawRowField fields 0, (decodeReadSymbol (rawRowField fields 1),
    (rawRowWorkCodes tapes fields).map decodeReadSymbol))

def rawRowNextStateCode (code : ℕ) : Option ℕ :=
  if code = 0 then none else some (code - 1)

def rawRowActFields (tapes : ℕ) (fields : List ℕ) :
    SignType × (List TapeAct × (Option ℕ × Option ℕ)) :=
  (decodeMove (rawRowField fields (2 + tapes)),
    (rawRowTapeActions tapes fields,
      (decodeReadSymbol (rawRowField fields (3 + 3 * tapes)),
        rawRowNextStateCode (rawRowField fields (4 + 3 * tapes)))))

def rawRowCandidate (tapes : ℕ) (fields : List ℕ) : Key × Act :=
  (⟨(rawRowKeyFields tapes fields).1, (rawRowKeyFields tapes fields).2.1,
      (rawRowKeyFields tapes fields).2.2⟩,
    ⟨(rawRowActFields tapes fields).1, (rawRowActFields tapes fields).2.1,
      (rawRowActFields tapes fields).2.2.1, (rawRowActFields tapes fields).2.2.2⟩)

/-- Runtime decoder: reject wrong-width or invalid-move rows; all payload fields are
then obtained with bounded range scans and indexed `getD`, not recursive splitting. -/
def decodeRawRowRuntime (tapes : ℕ) (fields : List ℕ) :
    Option (Key × Act) :=
  if fields.length = 5 + 3 * tapes && rawRowMovesValid tapes fields then
    some (rawRowCandidate tapes fields)
  else none

/-- On exact-width rows, the indexed fields are precisely those selected by the
successive `takeRawFields` calls in the specification parser. -/
theorem takeRawFields_eq_take_drop (n : ℕ) (fields : List ℕ) :
    takeRawFields n fields =
      if n ≤ fields.length then some (fields.take n, fields.drop n) else none := by
  induction n generalizing fields with
  | zero => simp [takeRawFields]
  | succ n ih =>
      cases fields with
      | nil => simp [takeRawFields]
      | cons field fields =>
          simp only [takeRawFields, ih, List.length_cons, List.take_succ_cons,
            List.drop_succ_cons]
          split_ifs <;> simp_all <;> omega

theorem rawRowField_range_eq_take (fields : List ℕ) (start count : ℕ)
    (hbound : start + count ≤ fields.length) :
    (List.range count).map (fun i => rawRowField fields (start + i)) =
      (fields.drop start).take count := by
  induction count generalizing start with
  | zero => simp
  | succ count ih =>
      rw [List.range_succ, List.map_append, List.map_singleton, ih start (by omega)]
      have hidx : start + count < fields.length := by omega
      simp [List.take_add_one, rawRowField, List.getElem?_drop, hidx]

theorem takeRawFields_length_relation {n : ℕ} {fields front rest : List ℕ}
    (h : takeRawFields n fields = some (front, rest)) :
    n + rest.length = fields.length := by
  rw [takeRawFields_eq_take_drop] at h
  split_ifs at h with hn
  · have hrest := congrArg Prod.snd (Option.some.inj h)
    change fields.drop n = rest at hrest
    rw [← hrest]
    simp [List.length_drop]
    omega

theorem decodeRawRow_some_length (tapes : ℕ) (fields : List ℕ)
    {row : Key × Act} (h : decodeRawRow tapes fields = some row) :
    fields.length = 5 + 3 * tapes := by
  cases fields with
  | nil => simp [decodeRawRow] at h
  | cons q fields =>
    cases fields with
    | nil => simp [decodeRawRow] at h
    | cons inputCode tail =>
      simp only [decodeRawRow, Bind.bind, Option.bind_eq_some_iff] at h
      rcases h with ⟨⟨workCodes, rest1⟩, htake1, hrest⟩
      cases rest1 with
      | nil => simp at hrest
      | cons inputMove rest2 =>
        simp only [Bind.bind, Option.bind_eq_some_iff] at hrest
        rcases hrest with ⟨⟨writeCodes, rest3⟩, htake2, hrest⟩
        simp only [Bind.bind, Option.bind_eq_some_iff] at hrest
        rcases hrest with ⟨⟨workMoves, rest4⟩, htake3, hrest⟩
        cases rest4 with
        | nil => simp at hrest
        | cons outputCode rest5 =>
          cases rest5 with
          | nil => simp at hrest
          | cons nextCode rest6 =>
            cases rest6 with
            | nil =>
              have h1 := takeRawFields_length_relation htake1
              have h2 := takeRawFields_length_relation htake2
              have h3 := takeRawFields_length_relation htake3
              simp only [List.length_cons, List.length_nil] at h1 hrest ⊢
              simp only [List.length_cons, List.length_nil] at h2 h3
              simp_all
              omega
            | cons extra rest => simp at hrest

theorem rawRowTapeActions_eq_zip (tapes : ℕ) (fields : List ℕ) :
    rawRowTapeActions tapes fields =
      ((rawRowWriteCodes tapes fields).map decodeWriteSymbol).zip
        ((rawRowWorkMoveCodes tapes fields).map decodeMove) := by
  unfold rawRowTapeActions rawRowWriteCodes rawRowWorkMoveCodes
  have hz := zipMapFstSnd ((List.range tapes).map fun i =>
    (decodeWriteSymbol (rawRowField fields (3 + tapes + i)),
      decodeMove (rawRowField fields (3 + 2 * tapes + i))))
  simpa [List.map_map, Function.comp_def] using hz.symm

theorem rawRowField_drop (fields : List ℕ) (start index : ℕ) :
    rawRowField fields (start + index) = rawRowField (fields.drop start) index := by
  simp [rawRowField, List.getElem?_drop]

theorem decodeRawRowRuntime_eq_decodeRawRow (tapes : ℕ) (fields : List ℕ) :
    decodeRawRowRuntime tapes fields = decodeRawRow tapes fields := by
  by_cases hwidth : fields.length = 5 + 3 * tapes
  · cases fields with
    | nil =>
      simp only [List.length_nil] at hwidth
      omega
    | cons q fields =>
      cases fields with
      | nil =>
        simp only [List.length_cons, List.length_nil] at hwidth
        omega
      | cons inputCode tail =>
        have htail : tail.length = 3 + 3 * tapes := by simp at hwidth; omega
        have htake1 : takeRawFields tapes tail =
            some (tail.take tapes, tail.drop tapes) := by
          rw [takeRawFields_eq_take_drop]
          simp [show tapes ≤ tail.length by omega]
        have hdrop1len : (tail.drop tapes).length = 3 + 2 * tapes := by
          simp [List.length_drop]
          omega
        cases hdrop1 : tail.drop tapes with
        | nil =>
          simp [hdrop1] at hdrop1len
          omega
        | cons inputMove rest1 =>
          have hrest1 : rest1.length = 2 + 2 * tapes := by
            simp [hdrop1] at hdrop1len
            omega
          have htake2 : takeRawFields tapes rest1 =
              some (rest1.take tapes, rest1.drop tapes) := by
            rw [takeRawFields_eq_take_drop]
            simp [show tapes ≤ rest1.length by omega]
          let rest2 := rest1.drop tapes
          have hrest2len : rest2.length = 2 + tapes := by
            dsimp [rest2]
            simp [List.length_drop]
            omega
          dsimp [rest2] at hrest2len
          have htake3 : takeRawFields tapes rest2 =
              some (rest2.take tapes, rest2.drop tapes) := by
            rw [takeRawFields_eq_take_drop]
            have hle : tapes ≤ (rest1.drop tapes).length := by
              simp [List.length_drop]
              omega
            change tapes ≤ rest2.length at hle
            simp [hle]
          have hfinalLen : (rest2.drop tapes).length = 2 := by
            dsimp [rest2]
            simp [List.length_drop]
            omega
          cases hfinal : rest2.drop tapes with
          | nil => simp [hfinal] at hfinalLen
          | cons outputCode rest5 =>
            cases rest5 with
            | nil => simp [hfinal] at hfinalLen
            | cons nextCode rest6 =>
              have hrest6 : rest6 = [] := by
                have : rest6.length = 0 := by simpa [hfinal] using hfinalLen
                cases rest6 <;> simp_all
              subst rest6
              have hwork : rawRowWorkCodes tapes (q :: inputCode :: tail) =
                  tail.take tapes := by
                unfold rawRowWorkCodes
                rw [rawRowField_range_eq_take (q :: inputCode :: tail) 2 tapes (by
                  simp; omega)]
                rfl
              have htailRest1 : tail.drop (tapes + 1) = rest1 := by
                have hh := congrArg (fun xs : List ℕ => xs.drop 1) hdrop1
                simpa [List.drop_drop] using hh
              have htailRest2 : tail.drop (tapes + 1 + tapes) = rest2 := by
                have hh := congrArg (fun xs : List ℕ => xs.drop tapes) htailRest1
                simpa [List.drop_drop] using hh
              have hwriteSegment : (q :: inputCode :: tail).drop (3 + tapes) = rest1 := by
                have hdropPrefix (n : ℕ) : (q :: inputCode :: tail).drop (2 + n) = tail.drop n := by
                  rw [show 2 + n = (n + 1) + 1 by omega]
                  simp [List.drop_succ_cons]
                rw [show 3 + tapes = 2 + (tapes + 1) by omega, hdropPrefix]
                exact htailRest1
              have hwrite : rawRowWriteCodes tapes (q :: inputCode :: tail) =
                  rest1.take tapes := by
                unfold rawRowWriteCodes
                rw [rawRowField_range_eq_take (q :: inputCode :: tail) (3 + tapes) tapes (by
                  simp; omega)]
                rw [hwriteSegment]
              have hmoveSegment : (q :: inputCode :: tail).drop (3 + 2 * tapes) = rest2 := by
                have hdropPrefix (n : ℕ) : (q :: inputCode :: tail).drop (2 + n) = tail.drop n := by
                  rw [show 2 + n = (n + 1) + 1 by omega]
                  simp [List.drop_succ_cons]
                rw [show 3 + 2 * tapes = 2 + (tapes + 1 + tapes) by omega, hdropPrefix]
                exact htailRest2
              have hmove : rawRowWorkMoveCodes tapes (q :: inputCode :: tail) =
                  rest2.take tapes := by
                unfold rawRowWorkMoveCodes
                rw [rawRowField_range_eq_take (q :: inputCode :: tail) (3 + 2 * tapes) tapes (by
                  simp; omega)]
                rw [hmoveSegment]
              have hfinalSegment : tail.drop (1 + 3 * tapes) = [outputCode, nextCode] := by
                have hindex : 1 + 3 * tapes = (tapes + 1 + tapes) + tapes := by omega
                rw [hindex, ← List.drop_drop, htailRest2]
                exact hfinal
              have hstate : rawRowField (q :: inputCode :: tail) 0 = q := by
                simp [rawRowField]
              have hinput : rawRowField (q :: inputCode :: tail) 1 = inputCode := by
                simp [rawRowField]
              have hfieldsTail : (q :: inputCode :: tail).drop 2 = tail := rfl
              have hinputMove : rawRowField (q :: inputCode :: tail) (2 + tapes) = inputMove := by
                rw [rawRowField_drop (q :: inputCode :: tail) 2 tapes, hfieldsTail]
                have ht : rawRowField tail tapes = rawRowField (tail.drop tapes) 0 := by
                  simpa [Nat.add_zero] using rawRowField_drop tail tapes 0
                rw [ht, hdrop1]
                rfl
              have houtput : rawRowField (q :: inputCode :: tail) (3 + 3 * tapes) = outputCode := by
                rw [show 3 + 3 * tapes = 2 + (1 + 3 * tapes) by omega]
                rw [rawRowField_drop (q :: inputCode :: tail) 2 (1 + 3 * tapes), hfieldsTail]
                have ht : rawRowField tail (1 + 3 * tapes) =
                    rawRowField (tail.drop (1 + 3 * tapes)) 0 := by
                  simpa [Nat.add_zero] using rawRowField_drop tail (1 + 3 * tapes) 0
                rw [ht, hfinalSegment]
                rfl
              have hnext : rawRowField (q :: inputCode :: tail) (4 + 3 * tapes) = nextCode := by
                rw [show 4 + 3 * tapes = 2 + ((1 + 3 * tapes) + 1) by omega]
                rw [rawRowField_drop (q :: inputCode :: tail) 2 ((1 + 3 * tapes) + 1), hfieldsTail]
                have ht : rawRowField tail ((1 + 3 * tapes) + 1) =
                    rawRowField (tail.drop (1 + 3 * tapes)) 1 := by
                  simpa using rawRowField_drop tail (1 + 3 * tapes) 1
                rw [ht, hfinalSegment]
                rfl
              have hvalid : rawRowMovesValid tapes (q :: inputCode :: tail) =
                  (validMove inputMove && (rest2.take tapes).all validMove) := by
                unfold rawRowMovesValid
                rw [hinputMove, hmove]
                change (validMove inputMove && (rest2.take tapes).all validMove) = _
                rfl
              have hcand : rawRowCandidate tapes (q :: inputCode :: tail) =
                  ((⟨q, decodeReadSymbol inputCode,
                      (tail.take tapes).map decodeReadSymbol⟩ : Key),
                    (⟨decodeMove inputMove,
                      (rest1.take tapes).map decodeWriteSymbol |>.zip
                        ((rest2.take tapes).map decodeMove),
                      decodeReadSymbol outputCode, rawRowNextStateCode nextCode⟩ : Act)) := by
                simp [rawRowCandidate, rawRowKeyFields, rawRowActFields,
                  hstate, hinput, hinputMove, houtput, hnext, hwork, hwrite, hmove,
                  rawRowTapeActions_eq_zip]
              have hparse : decodeRawRow tapes (q :: inputCode :: tail) =
                  if validMove inputMove && (rest2.take tapes).all validMove then
                    some ((⟨q, decodeReadSymbol inputCode,
                      (tail.take tapes).map decodeReadSymbol⟩ : Key),
                    (⟨decodeMove inputMove,
                      (rest1.take tapes).map decodeWriteSymbol |>.zip
                        ((rest2.take tapes).map decodeMove),
                      decodeReadSymbol outputCode, rawRowNextStateCode nextCode⟩ : Act))
                  else none := by
                dsimp [rest2] at htake3 hfinal
                simp [decodeRawRow, htake1, hdrop1, htake2, htake3, hfinal,
                  rawRowNextStateCode, rest2, List.map_take]
              simp [decodeRawRowRuntime, hwidth, hvalid, hcand, hparse,
                rawRowNextStateCode]
  · cases hparse : decodeRawRow tapes fields with
    | none => simp [decodeRawRowRuntime, hwidth, hparse]
    | some row =>
      have hlen := decodeRawRow_some_length tapes fields hparse
      contradiction

@[fun_prop] theorem decodeReadSymbol_efficient :
    ComputableTidilyInPolyTime decodeReadSymbol encUnary eSym := by
  unfold decodeReadSymbol
  fun_prop

@[fun_prop] theorem decodeWriteSymbol_efficient :
    ComputableTidilyInPolyTime decodeWriteSymbol encUnary (encOption eSym) := by
  unfold decodeWriteSymbol
  fun_prop

@[fun_prop] theorem decodeMove_efficient :
    ComputableTidilyInPolyTime decodeMove encUnary encSign := by
  have heq (k : ℕ) :
      ComputableTidilyInPolyTime (fun x : ℕ => decide (x = k)) encUnary encBool :=
    (ComputableTidilyInPolyTime.id' (encIn := encUnary)).decide_eq'
      (.const (encIn := encUnary) (encMid := encUnary) k)
  have h0 := heq 0
  have h1 := heq 1
  have h2 := heq 2
  have htail := h2.ite'
    (.const (encIn := encUnary) (encMid := encSign) SignType.pos)
    (.const (encIn := encUnary) (encMid := encSign) SignType.zero)
  have h01 := h1.ite'
    (.const (encIn := encUnary) (encMid := encSign) SignType.zero) htail
  have h := h0.ite'
    (.const (encIn := encUnary) (encMid := encSign) SignType.neg) h01
  exact h.of_enc_eq (fun n => by
    simp only [decodeMove]
    split <;> simp_all)

@[fun_prop] theorem rawRowField_efficient :
    ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => rawRowField p.1 p.2)
      (encPair (encList encUnary) encUnary) encUnary := by
  unfold rawRowField
  fun_prop

@[fun_prop] theorem rawRowWorkCodes_efficient :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => rawRowWorkCodes p.1 p.2)
      (encPair encUnary (encList encUnary)) (encList encUnary) := by
  unfold rawRowWorkCodes rawRowField
  fun_prop

@[fun_prop] theorem rawRowWriteCodes_efficient :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => rawRowWriteCodes p.1 p.2)
      (encPair encUnary (encList encUnary)) (encList encUnary) := by
  unfold rawRowWriteCodes rawRowField
  fun_prop

@[fun_prop] theorem rawRowWorkMoveCodes_efficient :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => rawRowWorkMoveCodes p.1 p.2)
      (encPair encUnary (encList encUnary)) (encList encUnary) := by
  unfold rawRowWorkMoveCodes rawRowField
  fun_prop

@[fun_prop] theorem rawRowTapeActions_efficient :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => rawRowTapeActions p.1 p.2)
      (encPair encUnary (encList encUnary)) (encList eTA) := by
  unfold rawRowTapeActions rawRowField
  fun_prop

@[fun_prop] theorem rawRowMoveValid_efficient :
    ComputableTidilyInPolyTime rawRowMoveValid encUnary encBool := by
  unfold rawRowMoveValid
  exact ComputableTidilyInPolyTime.unary_le' (.id' (encIn := encUnary)) (.const 2)

@[fun_prop] theorem rawRowMovesValid_efficient :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => rawRowMovesValid p.1 p.2)
      (encPair encUnary (encList encUnary)) encBool := by
  unfold rawRowMovesValid rawRowField
  fun_prop

@[fun_prop] theorem rawRowWidthValid_efficient :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ =>
      decide (p.2.length = 5 + 3 * p.1))
      (encPair encUnary (encList encUnary)) encBool := by
  have hlen : ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => p.2.length)
      (encPair encUnary (encList encUnary)) encUnary := by
    simpa [Function.comp_def] using
      (ComputableTidilyInPolyTime.length_list encUnary).comp
        (ComputableTidilyInPolyTime.snd encUnary (encList encUnary))
  have hwidth : ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => 5 + 3 * p.1)
      (encPair encUnary (encList encUnary)) encUnary := by
    fun_prop
  exact hlen.decide_eq' hwidth

@[fun_prop] theorem rawRowNextStateCode_efficient :
    ComputableTidilyInPolyTime rawRowNextStateCode encUnary (encOption encUnary) := by
  have hzero := (ComputableTidilyInPolyTime.id' (encIn := encUnary)).decide_eq'
    (.const (encIn := encUnary) (encMid := encUnary) 0)
  have hminus := ComputableTidilyInPolyTime.unary_sub.comp
    ((ComputableTidilyInPolyTime.id' (encIn := encUnary)).prod
      (.const (encIn := encUnary) (encMid := encUnary) 1))
  have hsome := (ComputableTidilyInPolyTime.optionSome encUnary).comp hminus
  have hnone : ComputableTidilyInPolyTime (fun _ : ℕ => (none : Option ℕ))
      encUnary (encOption encUnary) := .const none
  have h := hzero.ite_decide hnone hsome
  exact h.of_enc_eq (fun code => by simp [rawRowNextStateCode])

@[fun_prop] theorem rawRowKeyFields_efficient :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => rawRowKeyFields p.1 p.2)
      (encPair encUnary (encList encUnary))
      (encPair encUnary (encPair eSym (encList eSym))) := by
  unfold rawRowKeyFields
  fun_prop

@[fun_prop] theorem rawRowActFields_efficient :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => rawRowActFields p.1 p.2)
      (encPair encUnary (encList encUnary))
      (encPair encSign (encPair (encList eTA) (encPair eSym eSym))) := by
  unfold rawRowActFields
  fun_prop

@[fun_prop] theorem rawRowCandidate_efficient :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => rawRowCandidate p.1 p.2)
      (encPair encUnary (encList encUnary)) (encPair eKey eAct) := by
  have hk := rawRowKeyFields_efficient
  have ha := rawRowActFields_efficient
  have hk' : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℕ =>
        (⟨(rawRowKeyFields p.1 p.2).1, (rawRowKeyFields p.1 p.2).2.1,
          (rawRowKeyFields p.1 p.2).2.2⟩ : Key))
      (encPair encUnary (encList encUnary)) eKey :=
    hk.of_enc_eq (fun p => by simp [eKey_apply])
  have ha' : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℕ =>
        (⟨(rawRowActFields p.1 p.2).1, (rawRowActFields p.1 p.2).2.1,
          (rawRowActFields p.1 p.2).2.2.1, (rawRowActFields p.1 p.2).2.2.2⟩ : Act))
      (encPair encUnary (encList encUnary)) eAct :=
    ha.of_enc_eq (fun p => by simp [eAct_apply])
  exact (hk'.prod ha').of_enc_eq (fun p => rfl)

@[fun_prop] theorem decodeRawRowRuntime_efficient :
    ComputableTidilyInPolyTime
      (fun p : ℕ × List ℕ => decodeRawRowRuntime p.1 p.2)
      (encPair encUnary (encList encUnary)) (encOption (encPair eKey eAct)) := by
  have hguard : ComputableTidilyInPolyTime
      (fun p : ℕ × List ℕ =>
        decide (p.2.length = 5 + 3 * p.1) && rawRowMovesValid p.1 p.2)
      (encPair encUnary (encList encUnary)) encBool :=
    ComputableTidilyInPolyTime.bool_and'
      rawRowWidthValid_efficient rawRowMovesValid_efficient
  have hsome := (ComputableTidilyInPolyTime.optionSome (encPair eKey eAct)).comp
    rawRowCandidate_efficient
  have hnone : ComputableTidilyInPolyTime (fun _ : ℕ × List ℕ => (none : Option (Key × Act)))
      (encPair encUnary (encList encUnary)) (encOption (encPair eKey eAct)) := .const none
  have h := hguard.ite' hsome hnone
  exact h.of_enc_eq (fun p => by simp [decodeRawRowRuntime])

/-- The runtime decoder agrees with the legacy parser for every (including malformed)
input, and therefore inherits its exact acceptance semantics. -/
theorem decodeRawRow_efficient :
    ComputableTidilyInPolyTime (fun p : ℕ × List ℕ => decodeRawRow p.1 p.2)
      (encPair encUnary (encList encUnary)) (encOption (encPair eKey eAct)) := by
  have h := decodeRawRowRuntime_efficient
  exact h.of_enc_eq (fun ⟨tapes, fields⟩ => by
    rw [decodeRawRowRuntime_eq_decodeRawRow])

end AverageCaseComplexity.Completeness.TwoQuery
