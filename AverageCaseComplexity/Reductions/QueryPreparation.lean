module

public import AverageCaseComplexity.Reductions.OracleMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Equivalence
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic

@[expose] public section

namespace AverageCaseComplexity.OracleMachine

open Turing

variable {k : ℕ} {State : Type} {input : Word}

/-- Redirect each ordinary output instruction into the single query buffer.
This is a finite-control transformation and adds no instructions. It does not
submit a query: a subsequent control phase must perform that instruction. -/
noncomputable def writeQuery (M : MultiTapeTM k Bool State) :
    MultiTapeMachine k Bool State Unit Id where
  initial := M.q₀
  tr q symbol work _ :=
    let a := M.tr q symbol work
    .step { a with output := none } (fun _ => a.output) (fun _ => 0)

/-- Corresponding configurations: the source output is now the query buffer;
the previously received oracle answer and the actual output are untouched. -/
def queryConfig (cfg : Cfg k Bool State input) (answer output : Word) (head : ℤ) :
    MultiTapeMachine.Config k Bool State Unit input where
  tapes := { cfg with output := output }
  channels _ := ⟨cfg.output, answer, head⟩

@[simp] theorem queryConfig_state (cfg : Cfg k Bool State input)
    (answer output : Word) (head : ℤ) :
    (queryConfig cfg answer output head).tapes.state = cfg.state := rfl

/-- One redirected instruction preserves every ordinary tape update. -/
theorem step_queryConfig (cfg : Cfg k Bool State input) (a : Turing.Action k Bool State)
    (answer output : Word) (head : ℤ) :
    (queryConfig cfg answer output head).step { a with output := none }
        (fun _ => a.output) (fun _ => 0) =
      queryConfig (a.apply cfg) answer output head := by
  apply MultiTapeMachine.Config.ext
  · apply Cfg.ext <;> simp [queryConfig, MultiTapeMachine.Config.step, Turing.Action.apply]
  · funext u
    cases u
    apply MultiTapeMachine.Channel.ext <;> simp [queryConfig, MultiTapeMachine.Config.step,
      Turing.Action.apply]

/-- Exact simulation, including early halting. Query preparation preserves the
previous answer/output and has no oracle interactions for any oracle. -/
theorem runFrom_writeQuery (M : MultiTapeTM k Bool State) (L : Language)
    (fuel : ℕ) (cfg : Cfg k Bool State input) (answer output : Word) (head : ℤ) :
    runFrom (writeQuery M) L fuel (queryConfig cfg answer output head) =
      (queryConfig (M.runFrom cfg fuel) answer output head, []) := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
      rw [show M.runFrom cfg (fuel + 1) = M.runFrom (M.step cfg) fuel from
        Function.iterate_succ_apply M.step fuel cfg]
      cases hs : cfg.state with
      | none =>
          rw [M.step_of_halt hs]
          simp only [runFrom, queryConfig_state, hs]
          have hrun : M.runFrom cfg fuel = cfg := by
            exact M.runFrom_eq_of_halt cfg (Nat.zero_le _) hs
          rw [hrun]
      | some q =>
          simp only [runFrom, queryConfig_state, hs, writeQuery]
          rw [step_queryConfig]
          change runFrom (writeQuery M) L fuel
            (queryConfig ((M.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg) answer output head) = _
          rw [← M.step_of_state hs]
          exact ih (M.step cfg)

/-- From the standard blank-channel start, query preparation has exactly the
same clock and ordinary tape behavior as the original machine. -/
theorem run_writeQuery (M : MultiTapeTM k Bool State) (L : Language)
    (fuel : ℕ) (input : Word) :
    run (writeQuery M) L fuel input =
      (queryConfig (M.runFrom (M.initCfg input) fuel) [] [] 0, []) := by
  exact runFrom_writeQuery M L fuel (M.initCfg input) [] [] 0

/-- A tidy computation has restored the complete configuration by its clock,
not merely emitted the right output before a cutoff. -/
theorem runFrom_eq_wordsCfg (M : MultiTapeTM k Bool State) (input output : Word)
    (time space : ℕ) (h : M.ComputesTidilyInTimeAndSpace input output time space) :
    M.runFrom (M.initCfg input) time = wordsCfg input none (fun _ => []) output := by
  obtain ⟨p, hh, hl, ht, _⟩ := MultiTapeTM.computesTidily_iff.mp h
  have hhead : p.head = M.initCfg input := hh.trans (Cfg.init_eq_wordsCfg M.q₀ input).symm
  have hrun : M.runFrom (M.initCfg input) p.time = wordsCfg input none (fun _ => []) output :=
    hhead ▸ (MultiTapeTM.runPath_apply_eq_runFrom p (.last _)).symm.trans hl
  have hhalt : (M.runFrom (M.initCfg input) p.time).state = none := by rw [hrun]; rfl
  exact (M.runFrom_eq_of_halt _ ht hhalt).trans hrun

end AverageCaseComplexity.OracleMachine
