module

public import AverageCaseComplexity.Completeness.BoundedMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity
public import AverageCaseComplexity.Completeness.TupleDecodingRuntime

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery
open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Internal machine representation used between the binary parser and universal simulation. -/
def rawMachineData (m : RawFairMachine) : Desc × Desc × ℕ × ℕ :=
  (⟨m.tapes,m.initial,m.falseTable⟩, ⟨m.tapes,m.initial,m.trueTable⟩, m.falseSymbol, m.trueSymbol)

def rawMachineEncoding : RawFairMachine ↪ Word :=
  (⟨rawMachineData, by
    intro a b h
    cases a; cases b; simp only [rawMachineData, Prod.mk.injEq, Desc.mk.injEq] at h; grind⟩ :
    RawFairMachine ↪ Desc × Desc × ℕ × ℕ).trans
    (encPair eDesc (encPair eDesc (encPair encUnary encUnary)))

@[simp] theorem rawMachineEncoding_apply (m : RawFairMachine) : rawMachineEncoding m =
    encPair eDesc (encPair eDesc (encPair encUnary encUnary)) (rawMachineData m) := rfl

@[fun_prop] theorem rawMachineData_efficient : ComputableTidilyInPolyTime rawMachineData
    rawMachineEncoding (encPair eDesc (encPair eDesc (encPair encUnary encUnary))) :=
  (ComputableTidilyInPolyTime.id' (encIn := rawMachineEncoding)).of_enc_eq (fun _ => rfl)

@[fun_prop] theorem falseSymbol_efficient : ComputableTidilyInPolyTime RawFairMachine.falseSymbol
    rawMachineEncoding encUnary := rawMachineData_efficient.snd'.snd'.fst'

@[fun_prop] theorem trueSymbol_efficient : ComputableTidilyInPolyTime RawFairMachine.trueSymbol
    rawMachineEncoding encUnary := rawMachineData_efficient.snd'.snd'.snd'

open ComputableTidilyInPolyTime

/-- Translate Boolean input into the two symbols named in a machine's header. -/
theorem rawInputSymbols_efficient : ComputableTidilyInPolyTime
    (fun p : RawFairMachine × Word => rawInputSymbols p.1 p.2)
    (encPair rawMachineEncoding encBits) (encList encUnary) := by
  let f := fun p : RawFairMachine × Bool => if p.2 then p.1.trueSymbol else p.1.falseSymbol
  have hf : ComputableTidilyInPolyTime f (encPair rawMachineEncoding encBool) encUnary := by
    unfold f; fun_prop
  exact mapWith hf (fst rawMachineEncoding encBits) (bitsToList.comp (snd rawMachineEncoding encBits))

/-- A two-symbol answer must match the header exactly, with false given priority. -/
theorem rawAnswer_efficient : ComputableTidilyInPolyTime
    (fun p : RawFairMachine × List ℕ => rawAnswer p.1 p.2)
    (encPair rawMachineEncoding (encList encUnary)) answerEncoding := by
  let f := fun p : RawFairMachine × List ℕ =>
    if p.2 = [p.1.trueSymbol, p.1.falseSymbol] then some false
    else if p.2 = [p.1.trueSymbol, p.1.trueSymbol] then some true else none
  have h : ComputableTidilyInPolyTime f (encPair rawMachineEncoding (encList encUnary)) answerEncoding := by
    unfold f; fun_prop
  apply h.of_enc_eq
  rintro ⟨m, w⟩
  apply congrArg
  match w with
  | [] | [_] | _ :: _ :: _ :: _ => simp [rawAnswer, f]
  | [b,c] => simp [rawAnswer, f]; split_ifs <;> simp_all

private theorem outputBits_filter (m : RawFairMachine) (xs : List ℕ) :
    outputBits m xs = (xs.filter (fun i => decide (i = m.falseSymbol ∨ i = m.trueSymbol))).map
        (fun i => decide (i ≠ m.falseSymbol)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => by_cases hf : i = m.falseSymbol <;> by_cases ht : i = m.trueSymbol <;>
      simp [outputBits, hf, ht, ih] <;> split_ifs <;> simp_all

/-- Filter unknown numeric symbols, then map the two recognized symbols to bits. -/
theorem outputBits_efficient : ComputableTidilyInPolyTime
    (fun p : RawFairMachine × List ℕ => outputBits p.1 p.2)
    (encPair rawMachineEncoding (encList encUnary)) encBits := by
  have sel : ComputableTidilyInPolyTime
      (fun p : RawFairMachine × ℕ => decide (p.2 = p.1.falseSymbol ∨ p.2 = p.1.trueSymbol))
      (encPair rawMachineEncoding encUnary) encBool := by fun_prop
  have bit : ComputableTidilyInPolyTime (fun p : RawFairMachine × ℕ => decide (p.2 ≠ p.1.falseSymbol))
      (encPair rawMachineEncoding encUnary) encBool := by fun_prop
  let hm := fst rawMachineEncoding (encList encUnary)
  have hf := filterWith sel hm (snd rawMachineEncoding (encList encUnary))
  exact (listToBits.comp (mapWith bit hm hf)).of_enc_eq (fun p => by simp [outputBits_filter])


end AverageCaseComplexity.Completeness.TwoQuery
