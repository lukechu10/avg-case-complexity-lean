module

public import AverageCaseComplexity.Completeness.CompactCode
public import AverageCaseComplexity.Completeness.LengthNormalization
public import AverageCaseComplexity.Accuracy
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Basic

@[expose] public section

/-! # Checked bounded replay of raw fair-coin transition tables

A raw program has any finite number of work tapes and two transition tables,
selected by the fair coin. The code is a sequence of unary naturals separated by
`false`. Its header is `[tapes, q₀, false-symbol, true-symbol, |T₀|, |T₁|]`;
a row has `5 + 3*tapes` fields: `state, input-symbol, work-symbols...,
input-move, work-writes..., work-moves..., output-symbol, next-state`.
Read/output symbols use `0 = blank/absent`, `s + 1 = symbol s`; work writes
use `0 = no write`, `1 = erase`, `s + 2 = write symbol s`. Moves use
`0 = left`, `1 = stay`, `2 = right`, and next states use `0 = halt`,
`q + 1 = continue in q`. The two header symbols are distinct and represent
Boolean false/true on input and output.

Every parser stage is bounded by the source word: unary counts cannot exceed its
length, row parsing consumes only existing fields, and the simulator consumes no
more coins than supplied. Answer codes are decoded with `CompactCode`; bounded unary accuracy is exposed
with the exact `schemeInputEncoding` prefix and delimiter, without expanding an
unbounded accuracy. Sampler unary input is likewise virtualized only up to the
part observable within the coin clock.
-/

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing.MultiTapeTM.Universal

/-- Concatenated unary naturals, each terminated by a false delimiter. -/
def encodeRawFields (fields : List ℕ) : Word :=
  fields.flatMap fun n => List.replicate n true ++ [false]

/-- Checked linear parser for the unary-delimited natural fields. -/
def decodeRawFieldsAux : Word → ℕ → List ℕ → Option (List ℕ)
  | [], 0, fields => some fields.reverse
  | [], _ + 1, _ => none
  | true :: rest, count, fields => decodeRawFieldsAux rest (count + 1) fields
  | false :: rest, count, fields => decodeRawFieldsAux rest 0 (count :: fields)

def decodeRawFields (code : Word) : Option (List ℕ) :=
  decodeRawFieldsAux code 0 []

theorem decodeRawFieldsAux_replicate (n : ℕ) (tail : Word) (count : ℕ)
    (fields : List ℕ) :
    decodeRawFieldsAux (List.replicate n true ++ tail) count fields =
      decodeRawFieldsAux tail (count + n) fields := by
  induction n generalizing count with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, decodeRawFieldsAux]
      rw [ih]
      congr 1
      omega

/-- Parsing encoded fields appends them after any reversed accumulator. -/
theorem decodeRawFieldsAux_encodeRawFields (values acc : List ℕ) :
    decodeRawFieldsAux (encodeRawFields values) 0 acc = some (acc.reverse ++ values) := by
  induction values generalizing acc with
  | nil => simp [encodeRawFields, decodeRawFieldsAux]
  | cons n values ih =>
      simp only [encodeRawFields, List.flatMap_cons, List.append_assoc]
      change decodeRawFieldsAux
        (List.replicate n true ++ (false :: encodeRawFields values)) 0 acc = _
      rw [decodeRawFieldsAux_replicate n (false :: encodeRawFields values) 0 acc]
      simp only [decodeRawFieldsAux, Nat.zero_add]
      rw [ih (n :: acc)]
      simp [List.reverse_cons, List.append_assoc]

/-- The unary field codec round-trips every finite field list. -/
theorem decodeRawFields_encodeRawFields (fields : List ℕ) :
    decodeRawFields (encodeRawFields fields) = some fields := by
  simp [decodeRawFields, decodeRawFieldsAux_encodeRawFields]

def encodeReadSymbol : Option ℕ → ℕ
  | none => 0
  | some symbol => symbol + 1

def decodeReadSymbol (symbol : ℕ) : Option ℕ :=
  if symbol = 0 then none else some (symbol - 1)

@[simp] theorem decodeReadSymbol_encodeReadSymbol (symbol : Option ℕ) :
    decodeReadSymbol (encodeReadSymbol symbol) = symbol := by
  cases symbol with
  | none => rfl
  | some n => simp [decodeReadSymbol, encodeReadSymbol]

def encodeWriteSymbol : Option (Option ℕ) → ℕ
  | none => 0
  | some none => 1
  | some (some symbol) => symbol + 2

def decodeWriteSymbol (symbol : ℕ) : Option (Option ℕ) :=
  if symbol = 0 then none
  else if symbol = 1 then some none
  else some (some (symbol - 2))

@[simp] theorem decodeWriteSymbol_encodeWriteSymbol (symbol : Option (Option ℕ)) :
    decodeWriteSymbol (encodeWriteSymbol symbol) = symbol := by
  cases symbol with
  | none => rfl
  | some symbol => cases symbol with
    | none => rfl
    | some n => simp [decodeWriteSymbol, encodeWriteSymbol]

def decodeMove (move : ℕ) : SignType :=
  match move with
  | 0 => SignType.neg
  | 1 => SignType.zero
  | 2 => SignType.pos
  | _ => SignType.zero

def validMove (move : ℕ) : Bool := decide (move ≤ 2)

def encodeMove : SignType → ℕ
  | .neg => 0
  | .zero => 1
  | .pos => 2

@[simp] theorem decodeMove_encodeMove (move : SignType) :
    decodeMove (encodeMove move) = move := by
  cases move <;> rfl

def takeRawFields : ℕ → List ℕ → Option (List ℕ × List ℕ)
  | 0, fields => some ([], fields)
  | _ + 1, [] => none
  | n + 1, field :: fields => do
      let (front, rest) ← takeRawFields n fields
      return (field :: front, rest)

theorem takeRawFields_append_self (pre suffix : List ℕ) :
    takeRawFields pre.length (pre ++ suffix) = some (pre, suffix) := by
  induction pre with
  | nil => rfl
  | cons field pre ih => simp [takeRawFields, ih]

def decodeRawRow (tapes : ℕ) (fields : List ℕ) :
    Option (Turing.MultiTapeTM.Universal.Key × Turing.MultiTapeTM.Universal.Act) := do
  let q :: inputCode :: rest := fields | none
  let (workCodes, rest) ← takeRawFields tapes rest
  let inputMoveCode :: rest := rest | none
  let (writeCodes, rest) ← takeRawFields tapes rest
  let (workMoveCodes, rest) ← takeRawFields tapes rest
  let [outputCode, nextCode] := rest | none
  if (inputMoveCode :: workMoveCodes).all validMove then
    return (⟨q, decodeReadSymbol inputCode, workCodes.map decodeReadSymbol⟩,
      ⟨decodeMove inputMoveCode,
        (writeCodes.map decodeWriteSymbol).zip (workMoveCodes.map decodeMove),
        decodeReadSymbol outputCode,
        if nextCode = 0 then none else some (nextCode - 1)⟩)
  else none

/-- The canonical field representation of one universal transition. -/
def encodeRawRow (row : Key × Act) : List ℕ :=
  [row.1.state, encodeReadSymbol row.1.input] ++
    row.1.work.map encodeReadSymbol ++ [encodeMove row.2.inputTape] ++
    row.2.workTapes.map (encodeWriteSymbol ∘ Prod.fst) ++
    row.2.workTapes.map (encodeMove ∘ Prod.snd) ++
    [encodeReadSymbol row.2.output, row.2.state.map Nat.succ |>.getD 0]

/-- Flatten transition rows in their original lookup order. -/
def encodeRawRows (rows : List (Key × Act)) : List ℕ :=
  rows.flatMap encodeRawRow

def RawRowShape (tapes : ℕ) (row : Key × Act) : Prop :=
  row.1.work.length = tapes ∧ row.2.workTapes.length = tapes

theorem zipMapFstSnd (values : List (α × β)) :
    (values.map Prod.fst).zip (values.map Prod.snd) = values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [ih]

theorem decodeRawRow_encodeRawRow (tapes : ℕ) (row : Key × Act)
    (hshape : RawRowShape tapes row) :
    decodeRawRow tapes (encodeRawRow row) = some row := by
  rcases row with ⟨key, action⟩
  rcases key with ⟨state, input, work⟩
  rcases action with ⟨inputMove, workTapes, output, next⟩
  rcases hshape with ⟨hwork, hactions⟩
  change work.length = tapes at hwork
  change workTapes.length = tapes at hactions
  have ht (l r : List ℕ) (hl : l.length = tapes) :
      takeRawFields tapes (l ++ r) = some (l,r) := hl ▸ takeRawFields_append_self l r
  have valid (m : SignType) : validMove (encodeMove m) = true := by cases m <;> rfl
  cases next <;>
    simp [decodeRawRow, encodeRawRow, List.append_assoc, ht, hwork, hactions,
      Function.comp_def, valid, zipMapFstSnd]

def encodeRawPair (falseDesc trueDesc : Desc) (falseSymbol trueSymbol : ℕ) : Word :=
  encodeRawFields
    ([falseDesc.tapes, falseDesc.q₀, falseSymbol, trueSymbol,
      falseDesc.table.length, trueDesc.table.length] ++
      encodeRawRows falseDesc.table ++ encodeRawRows trueDesc.table)

/-- Parse exactly `fuel` rows, rejecting incomplete rows and trailing fields. -/
def decodeRawRowsAux (tapes : ℕ) : ℕ → List ℕ →
    Option (List (Turing.MultiTapeTM.Universal.Key × Turing.MultiTapeTM.Universal.Act))
  | 0, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, fields => do
      let width := 5 + 3 * tapes
      let (rowFields, rest) ← takeRawFields width fields
      let row ← decodeRawRow tapes rowFields
      let rows ← decodeRawRowsAux tapes fuel rest
      return row :: rows
  termination_by fuel _ => fuel

def decodeRawRows (tapes : ℕ) (fields : List ℕ) :
    Option (List (Turing.MultiTapeTM.Universal.Key × Turing.MultiTapeTM.Universal.Act)) :=
  let width := 5 + 3 * tapes
  decodeRawRowsAux tapes (fields.length / width) fields

def RawRowsShape (tapes : ℕ) (rows : List (Key × Act)) : Prop :=
  ∀ row ∈ rows, RawRowShape tapes row

theorem encodeRawRow_length (tapes : ℕ) (row : Key × Act)
    (hshape : RawRowShape tapes row) :
    (encodeRawRow row).length = 5 + 3 * tapes := by
  rcases row with ⟨key, action⟩
  rcases key with ⟨state, input, work⟩
  rcases action with ⟨inputMove, workTapes, output, next⟩
  have ⟨hwork, hactions⟩ := hshape
  change work.length = tapes at hwork
  change workTapes.length = tapes at hactions
  simp [encodeRawRow, hwork, hactions]
  omega

theorem encodeRawRows_length (tapes : ℕ) (rows : List (Key × Act))
    (hshape : RawRowsShape tapes rows) :
    (encodeRawRows rows).length = rows.length * (5 + 3 * tapes) := by
  induction rows with
  | nil => simp [encodeRawRows]
  | cons row rows ih =>
      have hr := hshape row (by simp)
      have hs : RawRowsShape tapes rows := by
        intro r hr
        exact hshape r (by simp [hr])
      change (encodeRawRow row ++ encodeRawRows rows).length =
        (row :: rows).length * (5 + 3 * tapes)
      rw [List.length_append, encodeRawRow_length tapes row hr, ih hs]
      simp only [List.length_cons]
      ring

theorem decodeRawRowsAux_encodeRawRows (tapes : ℕ) (rows : List (Key × Act))
    (hshape : RawRowsShape tapes rows) :
    decodeRawRowsAux tapes rows.length (encodeRawRows rows) = some rows := by
  induction rows with
  | nil => simp [decodeRawRowsAux, encodeRawRows]
  | cons row rows ih =>
      have hr := hshape row (by simp)
      have hs : RawRowsShape tapes rows := by
        intro r hr'
        exact hshape r (by simp [hr'])
      have hrow := encodeRawRow_length tapes row hr
      have htake : takeRawFields (5 + 3 * tapes)
          (encodeRawRow row ++ encodeRawRows rows) =
          some (encodeRawRow row, encodeRawRows rows) := by
        rw [← hrow]
        exact takeRawFields_append_self _ _
      change decodeRawRowsAux tapes (Nat.succ rows.length)
        (encodeRawRow row ++ encodeRawRows rows) = some (row :: rows)
      simp [decodeRawRowsAux, htake, decodeRawRow_encodeRawRow tapes row hr, ih hs]

theorem decodeRawRows_encodeRawRows (tapes : ℕ) (rows : List (Key × Act))
    (hshape : RawRowsShape tapes rows) :
    decodeRawRows tapes (encodeRawRows rows) = some rows := by
  dsimp [decodeRawRows]
  rw [encodeRawRows_length tapes rows hshape]
  have hw : 0 < 5 + 3 * tapes := by omega
  rw [show rows.length * (5 + 3 * tapes) /
      (5 + 3 * tapes) = rows.length by
        rw [Nat.mul_comm]
        exact Nat.mul_div_right _ hw]
  exact decodeRawRowsAux_encodeRawRows tapes rows hshape

/-- The two coin-selected transition tables of a checked raw machine. -/
structure RawFairMachine where
  tapes : ℕ
  initial : ℕ
  falseSymbol : ℕ
  trueSymbol : ℕ
  falseTable : List (Key × Act)
  trueTable : List (Key × Act)

/-- Decode the checked raw format. Invalid headers, row counts, and row actions
are rejected before any table-sized construction is performed. -/
def decodeRawFairMachine (code : Word) : Option RawFairMachine := do
  let fields ← decodeRawFields code
  match fields with
  | tapes :: initial :: falseSymbol :: trueSymbol :: falseCount :: trueCount :: rowFields => do
      if falseSymbol = trueSymbol then none else
      let rows ← decodeRawRows tapes rowFields
      if rows.length = falseCount + trueCount then
        return ⟨tapes, initial, falseSymbol, trueSymbol,
          rows.take falseCount, rows.drop falseCount⟩
      else none
  | _ => none

theorem decodeRawFairMachine_encodeRawPair
    (falseDesc trueDesc : Desc) (falseSymbol trueSymbol : ℕ)
    (htapes : trueDesc.tapes = falseDesc.tapes)
    (hinitial : trueDesc.q₀ = falseDesc.q₀)
    (hsymbol : falseSymbol ≠ trueSymbol)
    (hfalse : RawRowsShape falseDesc.tapes falseDesc.table)
    (htrue : RawRowsShape trueDesc.tapes trueDesc.table) :
    decodeRawFairMachine (encodeRawPair falseDesc trueDesc falseSymbol trueSymbol) =
      some ⟨falseDesc.tapes, falseDesc.q₀, falseSymbol, trueSymbol,
        falseDesc.table, trueDesc.table⟩ := by
  have hshape : RawRowsShape falseDesc.tapes (falseDesc.table ++ trueDesc.table) := by
    intro row hrow
    rcases List.mem_append.mp hrow with hrow | hrow
    · exact hfalse row hrow
    · simpa [htapes] using htrue row hrow
  have hrows : encodeRawRows falseDesc.table ++ encodeRawRows trueDesc.table =
      encodeRawRows (falseDesc.table ++ trueDesc.table) := by
    simp [encodeRawRows]
  simp [decodeRawFairMachine, encodeRawPair, decodeRawFields_encodeRawFields,
    hrows, decodeRawRows_encodeRawRows falseDesc.tapes
      (falseDesc.table ++ trueDesc.table) hshape, htapes, hinitial, hsymbol]

def rawInputSymbols (machine : RawFairMachine) (input : Word) : List ℕ :=
  input.map fun bit => if bit then machine.trueSymbol else machine.falseSymbol

def runTables (machine : RawFairMachine) (input : List ℕ) (coins : Word) : List ℕ :=
  let falseDesc : Desc := ⟨machine.tapes, machine.initial, machine.falseTable⟩
  let trueDesc : Desc := ⟨machine.tapes, machine.initial, machine.trueTable⟩
  let initialCfg : SCfg := init falseDesc
  let step (cfg : SCfg × List ℕ) (coin : Bool) : SCfg × List ℕ :=
    stepOut (if coin then trueDesc else falseDesc) input cfg
  (coins.foldl step (initialCfg, [])).2

def runRaw (machine : RawFairMachine) (input coins : Word) : List ℕ :=
  runTables machine (rawInputSymbols machine input) coins

def rawAnswer (machine : RawFairMachine) (output : List ℕ) : Answer :=
  match output with
  | [first, bit] =>
      if first = machine.trueSymbol then
        if bit = machine.falseSymbol then some false
        else if bit = machine.trueSymbol then some true
        else none
      else none
  | _ => none

/-- The observable prefix of `encodeSchemeInput x k`, bounded by the maximum
input-head position reachable in `steps` transitions. This preserves the exact
unary accuracy delimiter and raw input suffix without allocating `k` bits when
`k` is much larger than the clock. -/
def boundedSchemeInput (x : Word) (k : Accuracy) (steps : ℕ) : Word :=
  let cap := steps + 1
  if k.val < cap then
    List.replicate k.val true ++ [false] ++ x.take (cap - (k.val + 1))
  else List.replicate cap true

/-- Replay an actual decoded two-table fair-coin machine for at most
`coins.length` transitions. `code` is a CompactCode specialization: its header
is the raw table and its raw binary suffix is the positive accuracy. The machine
receives the exact bounded prefix of `schemeInputEncoding (x, accuracy)`.
Malformed compact or table codes give up. -/
def replayAnswer (code : Word) (x coins : Word) : Answer :=
  match decodeSpecializedCode code with
  | none => none
  | some (header, k) =>
      match decodeRawFairMachine header with
      | none => none
      | some machine =>
          rawAnswer machine (runRaw machine (boundedSchemeInput x k coins.length) coins)

def outputBits (machine : RawFairMachine) : List ℕ → Word
  | [] => []
  | symbol :: rest =>
      if symbol = machine.falseSymbol then false :: outputBits machine rest
      else if symbol = machine.trueSymbol then true :: outputBits machine rest
      else outputBits machine rest

/-- A unary input only needs to be materialized as far as a bounded run can
reach. The additional cell ensures that when `n` exceeds the clock, no blank
input cell is exposed during replay. -/
def boundedUnaryInput (n coinCount : ℕ) : Word :=
  List.replicate (min n (coinCount + 1)) true

/-- Replay a sampler for at most `coins.length` steps and truncate/pad its output
to exactly `n` bits. -/
def replaySample (code : Word) (n : ℕ) (coins : Word) : FixedWord n :=
  match decodeRawFairMachine code with
  | none => normalizeWord n []
  | some machine => normalizeWord n
      (outputBits machine (runRaw machine (boundedUnaryInput n coins.length) coins))


end AverageCaseComplexity.Completeness.TwoQuery
