import AverageCaseComplexity

open AverageCaseComplexity

-- Unconditional heuristic downward closure, with real deterministic machine certificates.
example {source target : DistributionalProblem}
    (hred : HeuristicallyReducible source target) (htarget : HeurP target) : HeurP source :=
  hred.toHeurP htarget

-- Pointwise errorless closure explicitly retains the support-preservation hypothesis.
example (T : PolyTimeOracleScheme) (source target : DistributionalProblem)
    (hred : ErrorlessReductionConditions T source target)
    (hsupport : T.QueriesSupported source target) (htarget : AvgP target) : AvgP source :=
  hred.toAvgP hsupport htarget

-- Global correctness of a supplied target solver is an alternative explicit repair.
example (T : PolyTimeOracleScheme) (source target : DistributionalProblem)
    (hred : ErrorlessReductionConditions T source target) (A : PolyTimeDeterministicScheme)
    (hA : A.run.ErrorlessConditions target)
    (hglobal : ∀ k y, IsAllowed target.language y (A.run y k)) : AvgP source :=
  hred.toAvgP_of_global_correct A hA hglobal

-- No unconditional errorless closure theorem is silently exported.
example : True := by
  fail_if_success have := ErrorlesslyReducible.toAvgP
  trivial

-- Fully supported target ensembles provide the additional hypothesis automatically.
example (source : DistributionalProblem) (L : Language)
    (hred : ErrorlesslyReducible source ⟨L, uniformEnsemble⟩)
    (htarget : AvgP ⟨L, uniformEnsemble⟩) : AvgP source := by
  apply hred.toAvgP_of_fullSupport ?_ htarget
  intro y
  apply (uniformEnsemble.wordMass_ne_zero_iff y).mp
  rw [Ensemble.wordMass_eq]
  simp

-- Three-way budget allocation is strict even when the exceptional-set bound is non-strict.
example (k : Accuracy) : k.triple.bound = k.bound / 3 := k.triple_bound

-- The target request remains well-defined at length zero and domination coefficient zero.
example (T : PolyTimeOracleScheme) (k : Accuracy) :
    0 < (T.simulationAccuracy 0 0 ([], k)).val :=
  (T.simulationAccuracy 0 0 ([], k)).property

-- Unary query-accuracy computation itself has a machine certificate.
example (T : PolyTimeOracleScheme) (c d : ℕ) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun a => (T.simulationAccuracy c d a).val) schemeInputEncoding
      Turing.MultiTapeTM.encUnary := T.simulationAccuracy_efficient c d

namespace SupportCaveat

-- A target solver may be wrong on a zero-mass query while satisfying its pointwise
-- correctness requirement. This tests a simulation issue, not a class separation.
noncomputable def targetEnsemble : Ensemble := fun _ => PMF.pure (fun _ => false)
def targetSolver : DeterministicScheme := fun x _ => if x = [true] then some true else some false

theorem targetSolver_correct : targetSolver.Correct ⟨fun _ => false, targetEnsemble⟩ := by
  intro k x hx
  obtain ⟨n, w, rfl, hw⟩ := hx
  have hw' : w = (fun _ => false) := by simpa [targetEnsemble, PMF.pure_apply] using hw
  subst w
  have hn : List.replicate n false ≠ [true] := by
    cases n <;> simp [List.replicate_succ]
  simp [targetSolver, IsAllowed, FixedWord.toWord, List.ofFn_const, hn]

example : targetEnsemble.wordMass [true] = 0 := by
  rw [Ensemble.wordMass_eq]
  have hn : ([true] : Word).get ≠ (fun _ => false) := by
    intro h
    have hh := congrFun h ⟨0, by decide⟩
    simp at hh
  simp [targetEnsemble, PMF.pure_apply]
  exact hn

-- This particular off-support-wrong solver is itself machine certified and
-- witnesses AvgP membership; correctness is genuinely only support-restricted.
def targetCertified : PolyTimeDeterministicScheme where
  run := targetSolver
  efficient := by
    have htest := (Turing.MultiTapeTM.ComputableTidilyInPolyTime.decide_eq
      Turing.MultiTapeTM.encBits).comp
        (schemeInput_word_efficient.prod
          (Turing.MultiTapeTM.ComputableTidilyInPolyTime.const [true]))
    have h : Turing.MultiTapeTM.ComputableTidilyInPolyTime _ schemeInputEncoding answerEncoding :=
      htest.cond (.const (some true)) (.const (some false))
    exact h.of_enc_eq (fun a => by simp [targetSolver])

example : AvgP ⟨fun _ => false, targetEnsemble⟩ := by
  refine ⟨targetCertified, ⟨targetSolver_correct, ?_⟩⟩
  intro k n
  have hz : targetEnsemble.prob n (fun x => targetCertified.run x k = none) = 0 := by
    apply Ensemble.prob_eq_zero_of_not_support
    intro x hx
    change ¬ targetSolver x k = none
    by_cases h : x = [true] <;> simp [targetSolver, h]
  rw [hz]
  exact k.bound_pos

-- The true query answer is false, but substitution returns true, not give-up.
example : Cslib.OracleComp.interpret (m := Id) (fun _ : Word => false)
    (Cslib.OracleComp.query (spec := fun _ : Word => Bool) [true]) = false := rfl
example (k : Accuracy) : Cslib.OracleComp.interpret (m := Option) (fun y => targetSolver y k)
    (Cslib.OracleComp.query (spec := fun _ : Word => Bool) [true]) = some true := rfl

end SupportCaveat
