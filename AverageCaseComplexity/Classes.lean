module

public import AverageCaseComplexity.Schemes
public import AverageCaseComplexity.Sampling

@[expose] public section

/-!
# Polynomial-time average-case and heuristic classes

The input is a word together with a unary reciprocal-accuracy parameter.
Both efficiency predicates use actual uniform finite-control machine certificates.
Randomized execution is strict polynomial time, not expected polynomial time.
The classes below do not assume `PSamp`; samplability is a separate restriction.
-/

namespace AverageCaseComplexity

/-- Fixed two-bit output encoding: `00` = give up, `10` = false, `11` = true. -/
def answerEncoding : Answer ↪ Word where
  toFun
    | none => [false, false]
    | some b => [true, b]
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all

/-- An executable deterministic scheme with a justified polynomial runtime. -/
structure PolyTimeDeterministicScheme where
  run : DeterministicScheme
  efficient : Turing.MultiTapeTM.ComputableTidilyInPolyTime
    (fun a : Word × Accuracy => run a.1 a.2) schemeInputEncoding answerEncoding

/-- An executable randomized scheme with a uniform strict polynomial clock. -/
structure PolyTimeRandomizedScheme where
  program : Word × Accuracy → Cslib.ProbComp Answer
  efficient : Cslib.Probability.IsPPTOn schemeInputEncoding answerEncoding program

/-- Output distribution of an executable randomized scheme. -/
noncomputable def PolyTimeRandomizedScheme.run (A : PolyTimeRandomizedScheme) :
    RandomizedScheme := fun x k => Cslib.ProbComp.eval (A.program (x, k))

/-- A deterministic machine is a randomized machine that ignores its coins. -/
def PolyTimeDeterministicScheme.randomize (A : PolyTimeDeterministicScheme) :
    PolyTimeRandomizedScheme where
  program a := pure (A.run a.1 a.2)
  efficient := A.efficient.isPPTOn

@[simp] theorem PolyTimeDeterministicScheme.run_randomize
    (A : PolyTimeDeterministicScheme) (x : Word) (k : Accuracy) :
    A.randomize.run x k = PMF.pure (A.run x k) := rfl

/-- Distributional problems solvable by polynomial-time errorless deterministic schemes. -/
def AvgP (P : DistributionalProblem) : Prop :=
  ∃ A : PolyTimeDeterministicScheme, A.run.ErrorlessConditions P

/-- Distributional problems solvable by polynomial-time randomized errorless schemes. -/
def AvgBPP (P : DistributionalProblem) : Prop :=
  ∃ A : PolyTimeRandomizedScheme, A.run.ErrorlessConditions P

/-- Distributional problems solvable by polynomial-time deterministic heuristic schemes. -/
def HeurP (P : DistributionalProblem) : Prop :=
  ∃ A : PolyTimeDeterministicScheme, A.run.HeuristicConditions P

/-- Distributional problems solvable by polynomial-time randomized heuristic schemes. -/
def HeurBPP (P : DistributionalProblem) : Prop :=
  ∃ A : PolyTimeRandomizedScheme, A.run.HeuristicConditions P

/-- Restrict a distributional class to exactly polynomial-time samplable ensembles. -/
def WithPSamp (C : DistributionalProblem → Prop) (P : DistributionalProblem) : Prop :=
  C P ∧ PSamp P.distribution

/-- A constant language has an efficient exact solver for every ensemble. -/
theorem AvgP.constant (b : Bool) (D : Ensemble) : AvgP ⟨fun _ => b, D⟩ := by
  refine ⟨{ run := fun _ _ => some b, efficient := .const (some b) }, ?_⟩
  constructor
  · intro k x hx
    exact Or.inl rfl
  · intro k n
    simp [Ensemble.prob, eventProb]

/-- The deterministic inclusion from §2.4, with the same runtime certificate. -/
theorem AvgP.toHeurP {P : DistributionalProblem} (h : AvgP P) : HeurP P := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, hA.toHeuristic⟩

/-- Deterministic average polynomial time is contained in randomized average polynomial time. -/
theorem AvgP.toAvgBPP {P : DistributionalProblem} (h : AvgP P) : AvgBPP P := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A.randomize, hA.randomize⟩

/-- Deterministic heuristic polynomial time is contained in randomized heuristic polynomial time. -/
theorem HeurP.toHeurBPP {P : DistributionalProblem} (h : HeurP P) : HeurBPP P := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A.randomize, hA.randomize⟩

/-- Any inclusion between distributional classes also holds under `PSamp`. -/
theorem WithPSamp.mono {C C' : DistributionalProblem → Prop}
    (h : ∀ P, C P → C' P) {P : DistributionalProblem} (hP : WithPSamp C P) :
    WithPSamp C' P := ⟨h P hP.1, hP.2⟩

end AverageCaseComplexity
