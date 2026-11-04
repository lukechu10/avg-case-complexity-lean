module

public import AverageCaseComplexity.Reductions.OracleScheme

@[expose] public section

namespace AverageCaseComplexity

/-- Substitute a deterministic partial solver for the oracle. A give-up answer aborts
execution; a give-up from the reduction itself is also preserved. Runtime is certified
separately, not assumed from this interpretation. -/
def PolyTimeOracleScheme.simulate (T : PolyTimeOracleScheme)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy) : Answer :=
  Option.join (Cslib.OracleComp.interpret (m := Option) (answer a) (T.program a))

namespace OracleMachine

/-- If the partial oracle answers every true-trace query correctly, its interpreted
execution agrees exactly with the true oracle. Queries can be adaptive. -/
theorem interpret_programFrom_eq_some {tapes states : ℕ} (M : OracleMachine tapes states)
    (L : Language) (answer : Word → Answer) (fuel : ℕ)
    (cfg : Turing.MultiTapeMachine.Config tapes Bool (Fin states) Unit input)
    (h : ∀ entry ∈ (runFrom M L fuel cfg).2, answer entry.1 = some entry.2) :
    Cslib.OracleComp.interpret (m := Option) answer (programFrom M fuel cfg) =
      some (runFrom M L fuel cfg).1 := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs]
    | some state =>
      cases ht : M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
      | step action symbol move =>
        simp only [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs, ht,
          pure_bind] at h ⊢
        exact ih _ h
      | query oracle next =>
        cases oracle
        have hh := h ((cfg.channels ()).queryBuffer, L (cfg.channels ()).queryBuffer)
          (by simp [runFrom, hs, ht])
        have htail : ∀ entry ∈
            (runFrom M L fuel (cfg.receive () next [L (cfg.channels ()).queryBuffer])).2,
            answer entry.1 = some entry.2 := by
          intro entry he
          exact h entry (by simp [runFrom, hs, ht, he])
        simp only [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs, ht,
          pure_bind, Cslib.OracleComp.interpret_bind, Cslib.OracleComp.interpret_map,
          Cslib.OracleComp.interpret_query, hh]
        exact ih _ htail

/-- A partial oracle that never supplies a wrong bit on the true trace either
aborts or returns exactly the true execution's final configuration. -/
theorem interpret_programFrom_eq_none_or_some {tapes states : ℕ}
    (M : OracleMachine tapes states) (L : Language) (answer : Word → Answer) (fuel : ℕ)
    (cfg : Turing.MultiTapeMachine.Config tapes Bool (Fin states) Unit input)
    (h : ∀ entry ∈ (runFrom M L fuel cfg).2,
      answer entry.1 = none ∨ answer entry.1 = some entry.2) :
    Cslib.OracleComp.interpret (m := Option) answer (programFrom M fuel cfg) = none ∨
    Cslib.OracleComp.interpret (m := Option) answer (programFrom M fuel cfg) =
      some (runFrom M L fuel cfg).1 := by
  induction fuel generalizing cfg with
  | zero => exact Or.inr rfl
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => right; simp [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs]
    | some state =>
      cases ht : M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
      | step action symbol move =>
        simp only [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs, ht,
          pure_bind] at h ⊢
        exact ih _ h
      | query oracle next =>
        cases oracle
        have hh := h ((cfg.channels ()).queryBuffer, L (cfg.channels ()).queryBuffer)
          (by simp [runFrom, hs, ht])
        have htail : ∀ entry ∈
            (runFrom M L fuel (cfg.receive () next [L (cfg.channels ()).queryBuffer])).2,
            answer entry.1 = none ∨ answer entry.1 = some entry.2 := by
          intro entry he
          exact h entry (by simp [runFrom, hs, ht, he])
        rcases hh with hh | hh
        · left
          simp [programFrom, Turing.MultiTapeMachine.runConfigFrom, hs, ht, hh]
        · simp only [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs, ht,
            pure_bind, Cslib.OracleComp.interpret_bind, Cslib.OracleComp.interpret_map,
            Cslib.OracleComp.interpret_query, hh]
          exact ih _ htail

/-- Every logged reply is the true oracle's answer to its request. -/
theorem reply_eq {tapes states : ℕ} (M : OracleMachine tapes states)
    (L : Language) (fuel : ℕ)
    (cfg : Turing.MultiTapeMachine.Config tapes Bool (Fin states) Unit input) :
    ∀ entry ∈ (runFrom M L fuel cfg).2, entry.2 = L entry.1 := by
  induction fuel generalizing cfg with
  | zero => simp [runFrom]
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none => simp [runFrom, hs]
    | some state =>
      cases ht : M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
      | step action symbol move => simpa [runFrom, hs, ht] using ih (cfg.step action symbol move)
      | query oracle next =>
        cases oracle
        simpa [runFrom, hs, ht] using ih (cfg.receive () next [L (cfg.channels ()).queryBuffer])

end OracleMachine

namespace PolyTimeOracleScheme

/-- No bad answer on the true trace implies exact agreement of the simulated answer. -/
theorem simulate_eq_of_answers (T : PolyTimeOracleScheme) (L : Language)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy)
    (h : ∀ y, T.Asks L a.1 a.2 y → answer a y = some (L y)) :
    T.simulate answer a = T.run L a.1 a.2 := by
  have hh := OracleMachine.interpret_programFrom_eq_some T.machine L (answer a)
    (T.clock a.1 a.2) (T.machine.initialConfig (schemeInputEncoding a)) (by
      intro entry he
      have ha := h entry.1 (List.mem_map.mpr ⟨entry, he, rfl⟩)
      have hr := OracleMachine.reply_eq T.machine L (T.clock a.1 a.2)
        (T.machine.initialConfig (schemeInputEncoding a)) entry he
      simpa only [hr] using ha)
  simp only [simulate, program, Cslib.OracleComp.interpret_map]
  change Option.join (Option.map _
    (Cslib.OracleComp.interpret (m := Option) (answer a)
      (OracleMachine.programFrom T.machine (T.clock a.1 a.2)
        (T.machine.initialConfig (schemeInputEncoding a))))) = _
  rw [hh]
  rfl

/-- If all true-trace replies are either correct or give-up, simulation is errorless
relative to the reduction's own answer. This hypothesis must include every query,
not merely queries outside a distributional exceptional set. -/
theorem simulate_eq_none_or_run (T : PolyTimeOracleScheme) (L : Language)
    (answer : Word × Accuracy → Word → Answer) (a : Word × Accuracy)
    (h : ∀ y, T.Asks L a.1 a.2 y → IsAllowed L y (answer a y)) :
    T.simulate answer a = none ∨ T.simulate answer a = T.run L a.1 a.2 := by
  have hh := OracleMachine.interpret_programFrom_eq_none_or_some T.machine L (answer a)
    (T.clock a.1 a.2) (T.machine.initialConfig (schemeInputEncoding a)) (by
      intro entry he
      have ha := h entry.1 (List.mem_map.mpr ⟨entry, he, rfl⟩)
      have hr := OracleMachine.reply_eq T.machine L (T.clock a.1 a.2)
        (T.machine.initialConfig (schemeInputEncoding a)) entry he
      rcases ha with ha | ha
      · exact Or.inr (by simpa only [hr] using ha)
      · exact Or.inl ha)
  rcases hh with hh | hh
  · left
    simp only [simulate, program, Cslib.OracleComp.interpret_map]
    change Option.join (Option.map _
      (Cslib.OracleComp.interpret (m := Option) (answer a)
        (OracleMachine.programFrom T.machine (T.clock a.1 a.2)
          (T.machine.initialConfig (schemeInputEncoding a))))) = none
    rw [hh]
    rfl
  · right
    simp only [simulate, program, Cslib.OracleComp.interpret_map]
    change Option.join (Option.map _
      (Cslib.OracleComp.interpret (m := Option) (answer a)
        (OracleMachine.programFrom T.machine (T.clock a.1 a.2)
          (T.machine.initialConfig (schemeInputEncoding a))))) = _
    rw [hh]
    rfl

/-- An additional condition, not part of Definition 2.2: every true-oracle query
on a source-supported input, at any accuracy, lands in target support. -/
def QueriesSupported (T : PolyTimeOracleScheme) (source target : DistributionalProblem) : Prop :=
  ∀ k x, source.distribution.Supports x →
    ∀ y, T.Asks target.language x k y → target.distribution.Supports y

end PolyTimeOracleScheme

end AverageCaseComplexity
