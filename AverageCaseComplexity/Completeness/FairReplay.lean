module

public import AverageCaseComplexity.Completeness.AnswerLaw
public import Complexity.Computability.Probabilistic.Sampling

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

/-- A coin tape sampled using only binary queries. -/
def fairTape : ℕ → Cslib.ProbComp Word
  | 0 => pure []
  | n + 1 => do
    let bit ← finTwoEquiv <$> Cslib.ProbComp.unifFin 1
    return bit :: (← fairTape n)

@[simp] theorem eval_fairTape (n : ℕ) :
    Cslib.ProbComp.eval (fairTape n) = Cslib.BitString.uniformList n := by
  induction n with
  | zero => simp [fairTape]
  | succ n ih =>
    rw [Cslib.BitString.uniformList_succ, ← Cslib.Probability.PMF.uniformOfFintype_map_equiv finTwoEquiv]
    simp [fairTape, ih, Function.comp_def]

/-- The binary-query implementation has the same certified sampler as `sampleList`. -/
theorem fairTape_efficient : Cslib.Probability.IsPPTOn Turing.MultiTapeTM.encUnary
    Turing.MultiTapeTM.encBits fairTape :=
  Cslib.Probability.isPPTOn_sampleList.congr (fun n => by simp)

/-- Number of coin tapes producing a particular answer under deterministic replay. -/
def replayCount (run : Word → Answer) (steps : ℕ) (a : Answer) : ℕ :=
  (Finset.univ.filter (fun coins : FixedWord steps => run (List.ofFn coins) = a)).card

theorem replay_mass (run : Word → Answer) (steps : ℕ) (a : Answer) :
    Cslib.ProbComp.eval (run <$> fairTape steps) a =
      (replayCount run steps a : ENNReal) / 2 ^ steps := by
  rw [Cslib.ProbComp.eval_map, eval_fairTape, Cslib.BitString.uniformList, PMF.map_comp,
    PMF.map_apply, tsum_fintype]
  simp [replayCount, ← Finset.sum_filter, div_eq_mul_inv, eq_comm]

/-- Integer comparisons suffice even on the boundary (one quarter exactly or a tie). -/
def exactReplayBit (run : Word → Answer) (steps : ℕ) (fallback : Bool) : Bool :=
  if 2 ^ steps ≤ 4 * replayCount run steps none then fallback
  else decide (replayCount run steps (some false) < replayCount run steps (some true))

theorem exactReplayBit_eq (run : Word → Answer) (steps : ℕ) (fallback : Bool) :
    exactReplayBit run steps fallback =
      fallbackBit (Cslib.ProbComp.eval (run <$> fairTape steps)) fallback := by
  unfold exactReplayBit fallbackBit frequentBit
  simp only [replay_mass]
  have h (a : Answer) : (((replayCount run steps a : ENNReal) / 2 ^ steps).toReal) =
      (replayCount run steps a : ℝ) / 2 ^ steps := by simp
  have hquarter : (1 / 4 : ENNReal) ≤ (replayCount run steps none : ENNReal) / 2 ^ steps ↔
      2 ^ steps ≤ 4 * replayCount run steps none := by
    rw [← ENNReal.toReal_le_toReal (by norm_num) (by finiteness), h]
    norm_num [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity : (0 : ℝ) < 2 ^ steps)]
    rw [mul_comm]
    norm_cast
  simp only [hquarter]
  simp [ENNReal.div_lt_div_iff_left (by positivity : (2 : ENNReal) ^ steps ≠ 0)
    (by finiteness : (2 : ENNReal) ^ steps ≠ ⊤)]

end AverageCaseComplexity.Completeness.TwoQuery
