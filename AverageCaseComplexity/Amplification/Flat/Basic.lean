module

public import AverageCaseComplexity.Classes
public import Complexity.Languages.Probabilistic.Repeat

@[expose] public section

/-! # Flat independent repetition and three-answer plurality -/

namespace AverageCaseComplexity

/-- Flat plurality, with ties ordered `none`, `some false`, `some true`. -/
def plurality (answers : List Answer) : Answer :=
  if answers.count (some false) ≤ answers.count none ∧
      answers.count (some true) ≤ answers.count none then none
  else if answers.count (some true) ≤ answers.count (some false) then some false
  else some true

/-- Finite independent repetitions followed by flat plurality. -/
noncomputable def flatPMF (p : PMF Answer) (count : ℕ) : PMF Answer :=
  (Cslib.Probability.PMF.pi (fun _ : Fin count => p)).map
    (fun answers => plurality (List.ofFn answers))

/-- Executable flat repetition, with independently sampled coins on each call. -/
def flatProgram (program : Cslib.ProbComp Answer) (count : ℕ) : Cslib.ProbComp Answer :=
  plurality <$> Cslib.OracleComp.replicate count program

@[simp] theorem eval_flatProgram (program : Cslib.ProbComp Answer) (count : ℕ) :
    Cslib.ProbComp.eval (flatProgram program count) = flatPMF program.eval count := by
  simp [flatProgram, flatPMF, Cslib.ProbComp.eval_replicate, PMF.map_comp,
    Function.comp_def]

/-- Every observation contributes to exactly one of the three answer counts. -/
theorem answer_counts_sum (answers : List Answer) :
    answers.count none + answers.count (some false) + answers.count (some true) =
      answers.length := by
  induction answers with
  | nil => simp
  | cons a answers ih =>
    cases a with
    | none => simp_all; omega
    | some b => cases b <;> simp_all <;> omega

/-- A plurality winner appears in at least a third of the observations. -/
theorem length_le_three_count_plurality (answers : List Answer) :
    answers.length ≤ 3 * answers.count (plurality answers) := by
  have hs := answer_counts_sum answers
  unfold plurality
  split_ifs <;> omega

end AverageCaseComplexity
