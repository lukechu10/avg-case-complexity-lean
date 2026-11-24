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

def decodeReadSymbol (symbol : ℕ) : Option (Option ℕ) :=
  if symbol = 0 then some none else some (some (symbol - 1))

def encodeWriteSymbol : Option (Option ℕ) → ℕ
  | none => 0
  | some none => 1
  | some (some symbol) => symbol + 2

def decodeWriteSymbol (symbol : ℕ) : Option (Option (Option ℕ)) :=
  if symbol = 0 then some none
  else if symbol = 1 then some (some none)
  else some (some (some (symbol - 2)))

def decodeMove (move : ℕ) : Option SignType :=
  match move with
  | 0 => some SignType.neg
  | 1 => some SignType.zero
  | 2 => some SignType.pos
  | _ => none

def encodeMove : SignType → ℕ
  | .neg => 0
  | .zero => 1
  | .pos => 2

def decodeRawRow (tapes : ℕ) (fields : List ℕ) :
    Option (Turing.MultiTapeTM.Universal.Key × Turing.MultiTapeTM.Universal.Act) := do
  if fields.length ≠ 5 + 3 * tapes then none else
  let q := fields.headD 0
  let inputSymbol ← decodeReadSymbol (fields[1]?.getD 0)
  let afterKey := fields.drop 2
  let workSymbols ← (afterKey.take tapes).mapM decodeReadSymbol
  let afterWork := afterKey.drop tapes
  let inputDirection ← decodeMove (afterWork.headD 3)
  let afterInputMove := afterWork.drop 1
  let workWrites ← (afterInputMove.take tapes).mapM decodeWriteSymbol
  let afterWrites := afterInputMove.drop tapes
  let workDirections ← (afterWrites.take tapes).mapM decodeMove
  let afterDirections := afterWrites.drop tapes
  let emitted ← decodeReadSymbol (afterDirections.headD 0)
  let nextCode := (afterDirections.drop 1).headD 0
  if (afterDirections.drop 2).isEmpty then
    let transitions := workWrites.zip workDirections
    return (⟨q, inputSymbol, workSymbols⟩,
      ⟨inputDirection, transitions, emitted,
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

theorem decodeRawRow_encodeRawRow (tapes : ℕ) (row : Key × Act)
    (hshape : RawRowShape tapes row) :
    decodeRawRow tapes (encodeRawRow row) = some row := by
  rcases row with ⟨key, action⟩
  rcases key with ⟨state, input, work⟩
  rcases action with ⟨inputMove, workTapes, output, next⟩
  simp [RawRowShape, encodeRawRow, decodeRawRow, encodeReadSymbol, decodeReadSymbol,
    encodeWriteSymbol, decodeWriteSymbol, encodeMove, decodeMove, hshape,
    List.mapM_map, Function.comp_def, Nat.add_sub_cancel]

def encodeRawPair (falseDesc trueDesc : Desc) (falseSymbol trueSymbol : ℕ) : Word :=
  encodeRawFields
    ([falseDesc.tapes, falseDesc.q₀, falseSymbol, trueSymbol,
      falseDesc.table.length, trueDesc.table.length] ++
      encodeRawRows falseDesc.table ++ encodeRawRows trueDesc.table)

def takeRawFields : ℕ → List ℕ → Option (List ℕ × List ℕ)
  | 0, fields => some ([], fields)
  | _ + 1, [] => none
  | n + 1, field :: fields => do
      let (front, rest) ← takeRawFields n fields
      return (field :: front, rest)

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

def rawInputSymbols (machine : RawFairMachine) (input : Word) : List ℕ :=
  input.map fun bit => if bit then machine.trueSymbol else machine.falseSymbol

def runTables (machine : RawFairMachine) (input : List ℕ) (coins : Word) : List ℕ :=
  let falseDesc : Desc := ⟨machine.tapes, machine.initial, machine.falseTable⟩
  let trueDesc : Desc := ⟨machine.tapes, machine.initial, machine.trueTable⟩
  let initialCfg : SCfg := init falseDesc
  let step (cfg : SCfg × List ℕ) (coin : Bool) : SCfg × List ℕ :=
    if cfg.1.state.isNone then cfg
    else
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
