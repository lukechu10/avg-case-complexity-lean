module

public import AverageCaseComplexity.Completeness.BoundedMachine
public import AverageCaseComplexity.Completeness.SourceClock
public import AverageCaseComplexity.Completeness.FairReplay
public import AverageCaseComplexity.Completeness.TailBounds
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Cslib

/-- Exact raw-table compiler specification, before supplying an accuracy suffix or
normalizing sampler output. Quantification is over actual finite-control machines. -/
def RawCompilerCorrect : Prop := ∀ {t : ℕ} {S : Type} [Finite S] (M : Turing.MultiTapePTM t Bool S),
  ∃ (header : Word) (machine : RawFairMachine), decodeRawFairMachine header = some machine ∧
    machine.trueSymbol ≠ machine.falseSymbol ∧ ∀ x coins : Word,
      runRaw machine x coins = rawInputSymbols machine (M.runClosedCoins coins x)

private theorem enlarge_clock (c d m : ℕ) (hm : 1 ≤ m) :
    max (c * m ^ d) m ≤ (c+1) * m ^ (d+1) := by
  rw [pow_succ, ← Nat.mul_assoc]
  apply max_le
  · exact (Nat.mul_le_mul_right _ (Nat.le_succ c)).trans (Nat.le_mul_of_pos_right _ hm)
  · exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (pow_pos hm _))

private theorem input_full (x : Word) (k : Accuracy) (steps : ℕ)
    (h : x.length + k.val + 2 ≤ steps) : boundedSchemeInput x k steps = schemeInputEncoding (x,k) := by
  simp [boundedSchemeInput, show k.val < steps+1 by omega, schemeInputEncoding, encodeSchemeInput]
  omega

private theorem decode_encoded_answer (m : RawFairMachine) (hne : m.trueSymbol ≠ m.falseSymbol)
    (a : Answer) : rawAnswer m (rawInputSymbols m (answerEncoding a)) = a := by
  cases a with
  | none => simp [answerEncoding, rawInputSymbols, rawAnswer, Ne.symm hne]
  | some b => cases b <;> simp [answerEncoding, rawInputSymbols, rawAnswer, hne]

private theorem outputBits_symbols (m : RawFairMachine) (hne : m.trueSymbol ≠ m.falseSymbol)
    (w : Word) : outputBits m (rawInputSymbols m w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simpa [rawInputSymbols, outputBits, hne] using ih

/-- Specialization changes the code, not the law: the replay sees the entire unary
input at the padded source clock. -/
theorem specialize_clocked_source (hraw : RawCompilerCorrect) (A : PolyTimeRandomizedScheme) :
    ∃ (header : Word) (c d : ℕ), ∀ x k,
      ProbComp.eval (replayAnswer (specializeCode header k) x <$>
        fairTape (c * (x.length + k.val + 2) ^ d + x.length + burnIn + 1)) = A.run x k := by
  obtain ⟨t,S,hS,M,c,d,_,hpad,_⟩ := A.efficient.exists_intrinsically_clocked_machine
  obtain ⟨header,machine,hdecode,hne,hheader⟩ := hraw M
  refine ⟨header,c+1,d+1,?_⟩
  intro x k
  let m := x.length + k.val + 2
  let steps := (c+1)*m^(d+1) + x.length + burnIn + 1
  have h := enlarge_clock c d m (by dsimp [m]; omega)
  have hsize : m ≤ steps := by dsimp [steps]; omega
  have hbound : c * ((schemeInputEncoding (x,k)).length+1)^d ≤ steps := by
    change c * ((encodeSchemeInput x k).length + 1)^d ≤ steps
    rw [encodeSchemeInput_length]; change c * m ^ d ≤ steps; dsimp [steps]; omega
  let decodeAns := rawAnswer machine ∘ rawInputSymbols machine
  have hlaw := congrArg (PMF.map decodeAns) (hpad (x,k) steps hbound)
  rw [Turing.MultiTapePTM.eval_runClosed_eq_map_coins, PMF.map_comp, PMF.map_comp] at hlaw
  have hid : decodeAns ∘ answerEncoding = id := funext (decode_encoded_answer machine hne)
  rw [hid, PMF.map_id] at hlaw
  rw [ProbComp.eval_map, eval_fairTape]
  refine Eq.trans ?_ hlaw
  apply Probability.PMF.map_congr_on_support
  intro coins hc
  have hc := BitString.length_of_mem_support_uniformList hc
  simp only [Function.comp_apply, replayAnswer, decodeSpecializedCode_specializeCode, hdecode, hc]
  rw [input_full x k _ hsize, hheader]
  rfl

/-- Sampling at the enlarged clock and reindexing to fixed-length words preserves
an exact sampler, including at length zero. -/
theorem replay_clocked_sampler (hraw : RawCompilerCorrect) (D : Ensemble) (hD : PSamp D) :
    ∃ (header : Word) (c d : ℕ), ∀ n, ProbComp.eval (replaySample header n <$>
      fairTape (c * (n+1)^d)) = D n := by
  obtain ⟨S,hS,hs⟩ := hD
  obtain ⟨t,State,hState,M,c,d,_,hpad,_⟩ := hS.exists_intrinsically_clocked_machine
  obtain ⟨header,machine,hdecode,hne,hheader⟩ := hraw M
  refine ⟨header,c+1,d+1,?_⟩
  intro n
  let steps := (c+1) * (n+1)^(d+1)
  have h := enlarge_clock c d (n+1) (by omega)
  have hlaw := congrArg (PMF.map (normalizeWord n)) (hpad n steps (by simp only [unaryEncoding_length]; exact le_trans (le_max_left ..) h))
  rw [Turing.MultiTapePTM.eval_runClosed_eq_map_coins, hs, Ensemble.wordDistribution] at hlaw
  simp only [Function.Embedding.coe_refl, PMF.map_comp, Function.id_comp] at hlaw
  have hid : normalizeWord n ∘ FixedWord.toWord = id := by
    funext y i; simp [normalizeWord, FixedWord.toWord]
  rw [hid, PMF.map_id] at hlaw
  rw [ProbComp.eval_map, eval_fairTape]
  refine Eq.trans ?_ hlaw
  apply Probability.PMF.map_congr_on_support
  intro coins hc
  have hc := BitString.length_of_mem_support_uniformList hc
  simp only [Function.comp_apply, replaySample, boundedUnaryInput, hc, hdecode, hheader, outputBits_symbols _ hne]
  rw [min_eq_left (by omega : n ≤ steps+1)]
  rfl

end AverageCaseComplexity.Completeness.TwoQuery
