module

public import AverageCaseComplexity.Classes

@[expose] public section

/-!
# Independent three-run plurality amplification

If two answers agree, return that answer. If all three differ, return the
first. The tie convention favors a run position, not a particular answer value.
Each boost uses three independent identically distributed executions, not a
shared random tape.
-/

namespace AverageCaseComplexity

/-- Three-answer plurality, breaking a three-way tie by the first observation. -/
def plurality3 (a b c : Answer) : Answer := if b = c then b else a

/-- One independent three-run boost at the distribution level. -/
noncomputable def boostPMF (p : PMF Answer) : PMF Answer :=
  p.bind fun a => p.bind fun b => p.bind fun c => PMF.pure (plurality3 a b c)

/-- Iterated boosting, using `3^depth` independent base executions. -/
noncomputable def amplifyPMF (p : PMF Answer) : ℕ → PMF Answer
  | 0 => p
  | depth + 1 => boostPMF (amplifyPMF p depth)

@[simp] theorem boostPMF_pure (a : Answer) : boostPMF (PMF.pure a) = PMF.pure a := by
  simp [boostPMF, plurality3]

@[simp] theorem amplifyPMF_pure (a : Answer) (depth : ℕ) :
    amplifyPMF (PMF.pure a) depth = PMF.pure a := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [amplifyPMF, ih]

/-- Executable independent three-run boost. -/
def boostProgram (program : Cslib.ProbComp Answer) : Cslib.ProbComp Answer := do
  let a ← program
  let b ← program
  let c ← program
  pure (plurality3 a b c)

/-- Executable iterated boost. The depth is fixed before choosing the input. -/
def amplifyProgram (program : Cslib.ProbComp Answer) : ℕ → Cslib.ProbComp Answer
  | 0 => program
  | depth + 1 => boostProgram (amplifyProgram program depth)

@[simp] theorem eval_boostProgram (program : Cslib.ProbComp Answer) :
    Cslib.ProbComp.eval (boostProgram program) = boostPMF (Cslib.ProbComp.eval program) := by
  simp [boostProgram, boostPMF, Cslib.ProbComp.eval_bind, PMF.map, Function.comp_def]

@[simp] theorem eval_amplifyProgram (program : Cslib.ProbComp Answer) (depth : ℕ) :
    Cslib.ProbComp.eval (amplifyProgram program depth) =
      amplifyPMF (Cslib.ProbComp.eval program) depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [amplifyProgram, amplifyPMF, ih]

end AverageCaseComplexity
