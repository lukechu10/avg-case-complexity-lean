module

public import AverageCaseComplexity.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Program

@[expose] public section

namespace AverageCaseComplexity

/-- A deterministic finite-control Turing machine with one Boolean-word oracle channel. -/
abbrev OracleMachine (tapes states : ℕ) :=
  Turing.MultiTapeMachine tapes Bool (Fin states) Unit Id

namespace OracleMachine

/-- Run for at most `fuel` instructions, retaining the final configuration and the
chronological sequence of oracle interactions. Each submitted request is the current query buffer;
the one-bit reply is installed on the answer tape. -/
def runFrom {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id) (L : Language) :
    ℕ → (cfg : Turing.MultiTapeMachine.Config tapes Bool State Unit input) →
      Turing.MultiTapeMachine.Config tapes Bool State Unit input × List (Word × Bool)
  | 0, cfg => (cfg, [])
  | fuel + 1, cfg =>
      match cfg.tapes.state with
      | none => (cfg, [])
      | some state =>
          match M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
          | .step action querySymbol answerMove =>
              runFrom M L fuel (cfg.step action querySymbol answerMove)
          | .query () next =>
              let request := (cfg.channels ()).queryBuffer
              let (final, trace) := runFrom M L fuel (cfg.receive () next [L request])
              (final, (request, L request) :: trace)

/-- A halted machine neither changes its tapes nor emits further queries. -/
theorem runFrom_halted {tapes : ℕ} {State : Type}
    (M : Turing.MultiTapeMachine tapes Bool State Unit Id) (L : Language)
    (fuel : ℕ) (cfg : Turing.MultiTapeMachine.Config tapes Bool State Unit input)
    (h : cfg.tapes.state = none) : runFrom M L fuel cfg = (cfg, []) := by
  cases fuel <;> simp [runFrom, h]

/-- Splitting an instruction budget concatenates the chronological traces. -/
theorem runFrom_add {tapes : ℕ} {State : Type}
    (M : Turing.MultiTapeMachine tapes Bool State Unit Id) (L : Language)
    (first second : ℕ) (cfg : Turing.MultiTapeMachine.Config tapes Bool State Unit input) :
    runFrom M L (first + second) cfg =
      let mid := runFrom M L first cfg
      let final := runFrom M L second mid.1
      (final.1, mid.2 ++ final.2) := by
  induction first generalizing cfg with
  | zero => simp [runFrom]
  | succ first ih =>
      cases hs : cfg.tapes.state with
      | none =>
          rw [runFrom_halted M L (first + 1 + second) cfg hs]
          simp [runFrom, hs, runFrom_halted M L second cfg hs]
      | some state =>
          cases ht : M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
          | step action symbol move =>
              simpa only [Nat.succ_add, runFrom, hs, ht] using ih (cfg.step action symbol move)
          | query oracle next =>
              cases oracle
              simpa only [Nat.succ_add, runFrom, hs, ht, Prod.fst, Prod.snd,
                List.cons_append] using congrArg
                  (fun result => (result.1, ((cfg.channels ()).queryBuffer,
                    L (cfg.channels ()).queryBuffer) :: result.2))
                  (ih (cfg.receive () next [L (cfg.channels ()).queryBuffer]))

/-- A genuinely halted run is unchanged by any larger instruction budget. -/
theorem runFrom_eq_of_halted {tapes : ℕ} {State : Type}
    (M : Turing.MultiTapeMachine tapes Bool State Unit Id) (L : Language)
    (first larger : ℕ) (cfg : Turing.MultiTapeMachine.Config tapes Bool State Unit input)
    (hle : first ≤ larger) (h : (runFrom M L first cfg).1.tapes.state = none) :
    runFrom M L larger cfg = runFrom M L first cfg := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [runFrom_add]
  dsimp only
  rw [runFrom_halted M L extra _ h]
  simp

/-- Run from the standard blank-channel initial configuration. -/
def run {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id) (L : Language)
    (fuel : ℕ) (input : Word) := runFrom M L fuel (M.initialConfig input)

/-- The generic machine-program execution with one typed oracle query per machine request. -/
def programFrom {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id) (fuel : ℕ)
    (cfg : Turing.MultiTapeMachine.Config tapes Bool State Unit input) :
    Cslib.OracleComp (fun _ : Word => Bool)
      (Turing.MultiTapeMachine.Config tapes Bool State Unit input) :=
  M.runConfigFrom (spec := fun _ : Word => Bool) pure
    (fun _ request => List.singleton <$> Cslib.OracleComp.query request) fuel cfg

/-- Generic program execution from blank channels. -/
def program {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id) (fuel : ℕ)
    (input : Word) : Cslib.OracleComp (fun _ : Word => Bool)
      (Turing.MultiTapeMachine.Config tapes Bool State Unit input) :=
  programFrom M fuel (M.initialConfig input)

/-- Interpreting the generic program by `L` recovers the final configuration of `runFrom`. -/
theorem interpret_programFrom {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id)
    (L : Language) (fuel : ℕ)
    (cfg : Turing.MultiTapeMachine.Config tapes Bool State Unit input) :
    Cslib.OracleComp.interpret (fun request : Word => (pure (L request) : Id Bool))
      (programFrom M fuel cfg) = (runFrom M L fuel cfg).1 := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
      cases hs : cfg.tapes.state with
      | none =>
          simp [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs]
          rfl
      | some state =>
          cases ht : M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
          | step action querySymbol answerMove =>
              simp only [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs, ht,
                pure_bind]
              have hi := ih (cfg.step action querySymbol answerMove)
              change Cslib.OracleComp.interpret
                (fun request : Word => (pure (L request) : Id Bool))
                (M.runConfigFrom (spec := fun _ : Word => Bool) pure
                  (fun _ request => List.singleton <$> Cslib.OracleComp.query request) fuel
                  (cfg.step action querySymbol answerMove)) = _ at hi
              exact hi
          | query oracle next =>
              cases oracle
              simp only [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs, ht,
                pure_bind, Cslib.OracleComp.interpret_bind,
                Cslib.OracleComp.interpret_map, Cslib.OracleComp.interpret_query]
              have hi := ih (cfg.receive () next [L (cfg.channels ()).queryBuffer])
              change Cslib.OracleComp.interpret
                (fun request : Word => (pure (L request) : Id Bool))
                (M.runConfigFrom (spec := fun _ : Word => Bool) pure
                  (fun _ request => List.singleton <$> Cslib.OracleComp.query request) fuel
                  (cfg.receive () next [L (cfg.channels ()).queryBuffer])) = _ at hi
              exact hi

/-- Interpreting the library machine program with a chronological query logger recovers
both the final configuration and exactly the trace recorded by `runFrom`.
The initial log is retained as a prefix; logging is semantic instrumentation. -/
theorem interpret_programFrom_withTrace {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id)
    (L : Language) (fuel : ℕ)
    (cfg : Turing.MultiTapeMachine.Config tapes Bool State Unit input)
    (seen : List (Word × Bool)) :
    (Cslib.OracleComp.interpret (m := StateM (List (Word × Bool)))
      (fun request : Word => (fun log => (L request, log ++ [(request, L request)])))
      (programFrom M fuel cfg)).run seen =
        ((runFrom M L fuel cfg).1, seen ++ (runFrom M L fuel cfg).2) := by
  induction fuel generalizing cfg seen with
  | zero =>
    simp [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom]
    rfl
  | succ fuel ih =>
    cases hs : cfg.tapes.state with
    | none =>
      simp [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs]
      rfl
    | some state =>
      cases ht : M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
      | step action querySymbol answerMove =>
        simpa only [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs, ht,
          pure_bind] using ih (cfg.step action querySymbol answerMove) seen
      | query oracle next =>
        cases oracle
        simp only [programFrom, runFrom, Turing.MultiTapeMachine.runConfigFrom, hs, ht,
          pure_bind, Cslib.OracleComp.interpret_bind, Cslib.OracleComp.interpret_map,
          Cslib.OracleComp.interpret_query]
        have hi := ih (cfg.receive () next [L (cfg.channels ()).queryBuffer])
          (seen ++ [((cfg.channels ()).queryBuffer, L (cfg.channels ()).queryBuffer)])
        simp only [List.append_assoc, List.singleton_append] at hi
        exact hi

/-- Every partial run makes at most one oracle call per unit of fuel. -/
theorem queryCount_runFrom_le {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id)
    (L : Language) (fuel : ℕ)
    (cfg : Turing.MultiTapeMachine.Config tapes Bool State Unit input) :
    ((runFrom M L fuel cfg).2).length ≤ fuel := by
  induction fuel generalizing cfg with
  | zero => simp [runFrom]
  | succ fuel ih =>
      cases hs : cfg.tapes.state with
      | none => simp [runFrom, hs]
      | some state =>
          cases ht : M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
          | step action querySymbol answerMove =>
              simp only [runFrom, hs, ht]
              exact Nat.le_succ_of_le (ih (cfg.step action querySymbol answerMove))
          | query oracle next =>
              cases oracle
              simp only [runFrom, hs, ht, List.length_cons]
              exact Nat.succ_le_succ (ih (cfg.receive () next [L (cfg.channels ()).queryBuffer]))

/-- A query submitted during a partial run is no longer than the initial buffer plus
its remaining instruction budget. -/
theorem requestLength_runFrom_le {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id)
    (L : Language) (fuel : ℕ)
    (cfg : Turing.MultiTapeMachine.Config tapes Bool State Unit input) :
    ∀ entry ∈ (runFrom M L fuel cfg).2,
      entry.1.length ≤ (cfg.channels ()).queryBuffer.length + fuel := by
  induction fuel generalizing cfg with
  | zero => simp [runFrom]
  | succ fuel ih =>
      cases hs : cfg.tapes.state with
      | none => simp [runFrom, hs]
      | some state =>
          cases ht : M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
          | step action querySymbol answerMove =>
              simp only [runFrom, hs, ht]
              intro entry he
              have h := ih (cfg.step action querySymbol answerMove) entry he
              have hbuf : ((cfg.step action querySymbol answerMove).channels ()).queryBuffer.length ≤
                  (cfg.channels ()).queryBuffer.length + 1 := by
                have hwrite : ((querySymbol ()).toList).length ≤ 1 := by
                  cases querySymbol () <;> simp
                simp [Turing.MultiTapeMachine.Config.step, List.length_append]
              omega
          | query oracle next =>
              cases oracle
              simp only [runFrom, hs, ht, List.mem_cons]
              intro entry he
              rcases he with hhead | htail
              · cases hhead
                simpa only [Prod.fst] using
                  (Nat.le_add_right (cfg.channels ()).queryBuffer.length (fuel + 1))
              · have h := ih (cfg.receive () next [L (cfg.channels ()).queryBuffer]) entry htail
                have hzero : ((cfg.receive () next [L (cfg.channels ()).queryBuffer]).channels ()).queryBuffer.length = 0 := by
                  rfl
                omega

/-- From blank channels, every oracle request has length at most the clock. -/
theorem requestLength_run_le {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id)
    (L : Language) (fuel : ℕ) (input : Word) :
    ∀ entry ∈ (run M L fuel input).2, entry.1.length ≤ fuel := by
  simpa [run, Turing.MultiTapeMachine.initialConfig] using
    (requestLength_runFrom_le M L fuel (M.initialConfig input))

/-- The blank-channel run also satisfies the query-count clock bound. -/
theorem queryCount_run_le {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id)
    (L : Language) (fuel : ℕ) (input : Word) :
    (run M L fuel input).2.length ≤ fuel := by
  exact queryCount_runFrom_le M L fuel (M.initialConfig input)

/-- Interpreting the generic blank-channel program by `L` recovers the final configuration. -/
theorem interpret_program {tapes : ℕ} {State : Type} (M : Turing.MultiTapeMachine tapes Bool State Unit Id)
    (L : Language) (fuel : ℕ) (input : Word) :
    Cslib.OracleComp.interpret (fun request : Word => (pure (L request) : Id Bool))
      (program M fuel input) = (run M L fuel input).1 := by
  exact interpret_programFrom M L fuel (M.initialConfig input)

end OracleMachine

end AverageCaseComplexity
