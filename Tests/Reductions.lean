import AverageCaseComplexity

open AverageCaseComplexity

-- D(y) uses the ensemble component at y's own length, not a global word PMF.
example (D : Ensemble) (n : ℕ) (w : FixedWord n) : D.wordMass w.toWord = D n w := by simp
example (D : Ensemble) (y : Word) : D.wordMass y ≠ 0 ↔ D.Supports y :=
  D.wordMass_ne_zero_iff y
example (y : Word) : uniformEnsemble.wordMass y = (2 ^ y.length : ENNReal)⁻¹ := by
  rw [Ensemble.wordMass_eq]
  simp

namespace ReductionTests

-- A genuine finite-control, zero-work-tape machine, not an arbitrary function with a cost.
def emit {states : ℕ} (bit : Bool) (next : Option (Fin states)) :
    Turing.MultiTapeMachine.Action 0 Bool (Fin states) Unit :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := next }
    (fun _ => none) (fun _ => 0)

def constantMachine (bit : Bool) : OracleMachine 0 2 where
  initial := 0
  tr state _ _ _ := if state = 0 then emit true (some 1) else emit bit none

-- Emit the two-bit encoding, then actually halt after exactly two instructions.
def constantScheme (bit : Bool) : PolyTimeOracleScheme where
  workTapes := 0
  stateCount := 2
  machine := constantMachine bit
  coefficient := 2
  degree := 0
  halts := by
    intro L a
    simp [oracleClock, OracleMachine.run, OracleMachine.runFrom, constantMachine, emit,
      Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init,
      Turing.MultiTapeMachine.Config.step, Turing.Action.apply]
  output_valid := by
    intro L a
    refine ⟨some bit, ?_⟩
    simp [oracleClock, OracleMachine.run, OracleMachine.runFrom, constantMachine, emit,
      Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init,
      Turing.MultiTapeMachine.Config.step, Turing.Action.apply, answerEncoding]

@[simp] theorem constant_run (bit : Bool) (L : Language) (x : Word) (k : Accuracy) :
    (constantScheme bit).run L x k = some bit := by
  simp [PolyTimeOracleScheme.run, PolyTimeOracleScheme.execution, PolyTimeOracleScheme.clock,
    constantScheme, oracleClock, OracleMachine.run, OracleMachine.runFrom, constantMachine,
    emit, Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init,
    Turing.MultiTapeMachine.Config.step, Turing.Action.apply, decodeOracleAnswer]

@[simp] theorem constant_trace (bit : Bool) (L : Language) (x : Word) (k : Accuracy) :
    (constantScheme bit).trace L x k = [] := by
  simp [PolyTimeOracleScheme.trace, PolyTimeOracleScheme.execution, PolyTimeOracleScheme.clock,
    constantScheme, oracleClock, OracleMachine.run, OracleMachine.runFrom, constantMachine,
    emit, Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init,
    Turing.MultiTapeMachine.Config.step, Turing.Action.apply]

-- The next call depends on the preceding reply: true causes a repeated query,
-- false does not. Both paths output the exact answer to the empty-word query.
def adaptiveMachine : OracleMachine 0 4 where
  initial := 0
  tr state _ _ answers :=
    if state = 0 then .query () 1
    else if state = 1 then
      if answers () = some true then .query () 2 else emit true (some 3)
    else if state = 2 then emit true (some 3)
    else emit ((answers ()).getD false) none

def adaptiveScheme : PolyTimeOracleScheme where
  workTapes := 0
  stateCount := 4
  machine := adaptiveMachine
  coefficient := 4
  degree := 0
  halts := by
    intro L a
    cases h : L [] <;>
      simp [oracleClock, OracleMachine.run, OracleMachine.runFrom, adaptiveMachine, emit,
        Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init,
        Turing.MultiTapeMachine.Config.step, Turing.MultiTapeMachine.Config.receive,
        Turing.MultiTapeMachine.Config.answerSymbols, Turing.MultiTapeMachine.Channel.answerSymbol,
        Turing.Action.apply, h]
  output_valid := by
    intro L a
    refine ⟨some (L []), ?_⟩
    cases h : L [] <;>
      simp [oracleClock, OracleMachine.run, OracleMachine.runFrom, adaptiveMachine, emit,
        Turing.MultiTapeMachine.initialConfig, Turing.Cfg.init,
        Turing.MultiTapeMachine.Config.step, Turing.MultiTapeMachine.Config.receive,
        Turing.MultiTapeMachine.Config.answerSymbols, Turing.MultiTapeMachine.Channel.answerSymbol,
        Turing.Action.apply, answerEncoding, h]

example : adaptiveScheme.trace (fun _ => true) [] ⟨1, by decide⟩ =
    [([], true), ([], true)] := rfl
example : adaptiveScheme.trace (fun _ => false) [] ⟨1, by decide⟩ = [([], false)] := rfl

-- The trace records two calls; Ask is still just a zero-one event.
example : (adaptiveScheme.queryWords (fun _ => true) [] ⟨1, by decide⟩).count [] = 2 := rfl
example : adaptiveScheme.askIndicator (fun _ => true) [] ⟨1, by decide⟩ [] = 1 := rfl
example : adaptiveScheme.askIndicator (fun _ => true) [] ⟨1, by decide⟩ [false] = 0 := rfl

-- Consequently queryMass is one, not two, at every source length.
example (D : Ensemble) (n : ℕ) (k : Accuracy) :
    adaptiveScheme.queryMass (fun _ => true) D k n ∅ [] = 1 := by
  have hasks (x : FixedWord n) : adaptiveScheme.Asks (fun _ => true) x.toWord k [] := by
    exact List.mem_cons_self
  simpa only [PolyTimeOracleScheme.queryMass, Set.mem_empty_iff_false, not_false_eq_true,
    hasks, and_self] using eventProb_true (D n)

-- Actual adaptive executions through the new aborting simulator.
example : adaptiveScheme.simulate (fun _ _ => some false) ([], ⟨1, by decide⟩) =
    some false := rfl
example : adaptiveScheme.simulate (fun _ _ => some true) ([], ⟨1, by decide⟩) =
    some true := rfl
example : adaptiveScheme.simulate (fun _ _ => none) ([], ⟨1, by decide⟩) = none := rfl

-- The simulator has a genuine deterministic machine certificate, not just output semantics.
example : Turing.MultiTapeTM.ComputableTidilyInPolyTime
    (adaptiveScheme.simulate (fun _ _ => some false)) schemeInputEncoding answerEncoding :=
  adaptiveScheme.simulate_efficient (answer := fun _ _ => some false) (.const (some false))

-- A source-dependent exponential envelope stays linear in the quantitative
-- certificate for this actual adaptive finite transition table.
example : ∃ d, Turing.MultiTapeTM.ComputableTidilyInO
    (adaptiveScheme.simulate (fun _ _ => some false)) schemeInputEncoding answerEncoding
    (fun a => ((schemeInputEncoding a).length + 1) ^ d * (2 ^ (a.1.length ^ 2) + 1))
    (fun a => ((schemeInputEncoding a).length + 1) ^ d * (2 ^ (a.1.length ^ 2) + 1)) := by
  have hc : Turing.MultiTapeTM.ComputableTidilyInO
      (fun _ : (Word × Accuracy) × Word => (some false : Answer))
      (Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits) answerEncoding
      (fun p => ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits p).length + 1) ^ 1 +
        2 ^ (p.1.1.length ^ 2))
      (fun p => ((Turing.MultiTapeTM.encPair schemeInputEncoding Turing.MultiTapeTM.encBits p).length + 1) ^ 1 +
        2 ^ (p.1.1.length ^ 2)) :=
    (Turing.MultiTapeTM.ComputableTidilyInO.const (some false)).mono_le
      (fun p => by simp only [pow_one]; exact (Nat.le_succ _).trans (Nat.le_add_right _ _))
      (fun p => by simp only [pow_one]; exact (Nat.le_succ _).trans (Nat.le_add_right _ _))
  exact adaptiveScheme.simulate_arbitrary_inO (answer := fun _ _ => some false)
    (H := fun a => 2 ^ (a.1.length ^ 2)) hc

-- A small reduction-witness sanity check.
example (bit : Bool) (D : Ensemble) (target : DistributionalProblem) :
    ErrorlesslyReducible ⟨fun _ => bit, D⟩ target := by
  refine ⟨constantScheme bit, ⟨?_, ?_⟩⟩
  · constructor
    · intro k x hx
      simp [IsAllowed]
    · intro k n
      simp [Ensemble.prob, eventProb]
  · refine ⟨0, 0, ?_⟩
    intro k n
    refine ⟨∅, ?_, ?_⟩
    · change eventProb (D n) (fun _ => False) ≤ k.bound
      simp
    · intro y
      simp [PolyTimeOracleScheme.queryMass, PolyTimeOracleScheme.Asks,
        PolyTimeOracleScheme.queryWords, PolyTimeOracleScheme.dominationFactor, eventProb]

-- General heuristic error includes an incorrect Boolean output, without a
-- separate pointwise-correctness condition.
example (D : Ensemble) (target : DistributionalProblem) :
    ¬ HeuristicReductionConditions (constantScheme true) ⟨fun _ => false, D⟩ target := by
  intro h
  have bad := h.heuristic ⟨1, by decide⟩ 0
  change D.prob 0 (fun x => (constantScheme true).run target.language x ⟨1, by decide⟩ ≠
    some false) < Accuracy.bound ⟨1, by decide⟩ at bad
  simp only [constant_run] at bad
  simp [Ensemble.prob, Accuracy.bound] at bad

end ReductionTests
