import AverageCaseComplexity

open AverageCaseComplexity

-- Both Boolean answers have a machine-certified exact constant solver.
example (D : Ensemble) : AvgP ⟨fun _ => false, D⟩ := AvgP.constant false D
example (D : Ensemble) : AvgP ⟨fun _ => true, D⟩ := AvgP.constant true D

-- These are actual class inclusions, including the runtime certificates.
example (D : Ensemble) : AvgBPP ⟨fun _ => true, D⟩ :=
  (AvgP.constant true D).toAvgBPP

example (D : Ensemble) : HeurP ⟨fun _ => false, D⟩ :=
  (AvgP.constant false D).toHeurP

example (D : Ensemble) : HeurBPP ⟨fun _ => false, D⟩ :=
  (AvgP.constant false D).toHeurP.toHeurBPP

-- Samplability remains an explicit restriction, not an assumption on all ensembles.
example (P : DistributionalProblem) (h : WithPSamp AvgP P) : WithPSamp AvgBPP P :=
  WithPSamp.mono (fun _ hP => hP.toAvgBPP) h

-- Always giving up cannot satisfy usefulness, even at the weakest request k = 1.
example (P : DistributionalProblem) :
    ¬ DeterministicScheme.Useful (fun _ _ => none) P := by
  intro h
  have hbad := h ⟨1, by decide⟩ 0
  simp [Ensemble.prob, Accuracy.bound] at hbad

-- A point mass is judged by the correct event: give-up is not a wrong Boolean answer.
example (L : Language) (x : Word) : wrongProb L x (PMF.pure none) = 0 := by
  simp [wrongProb, IsAllowed]

example (L : Language) (x : Word) : failureProb L x (PMF.pure none) = 1 := by
  simp [failureProb]
