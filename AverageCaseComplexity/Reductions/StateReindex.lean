module

public import AverageCaseComplexity.Reductions.OracleMachine

@[expose] public section

namespace AverageCaseComplexity.OracleMachine

open Turing Turing.MultiTapeMachine

variable {k : ℕ} {S T : Type} {input : Word}

/-- Reindex every live control state while leaving the tape contents and oracle
channels unchanged. -/
def mapCfg (e : S ≃ T) (cfg : Config k Bool S Unit input) :
    Config k Bool T Unit input :=
  { cfg with tapes := cfg.tapes.mapState (Option.map e) }

@[simp] theorem mapCfg_state (e : S ≃ T) (cfg : Config k Bool S Unit input) :
    (mapCfg e cfg).tapes.state = cfg.tapes.state.map e := rfl

@[simp] theorem mapCfg_inputSymbol (e : S ≃ T) (cfg : Config k Bool S Unit input) :
    (mapCfg e cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem mapCfg_workTapeSymbols (e : S ≃ T) (cfg : Config k Bool S Unit input) :
    (mapCfg e cfg).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem mapCfg_output (e : S ≃ T) (cfg : Config k Bool S Unit input) :
    (mapCfg e cfg).tapes.output = cfg.tapes.output := rfl

@[simp] theorem mapCfg_answerSymbols (e : S ≃ T) (cfg : Config k Bool S Unit input) :
    (mapCfg e cfg).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem mapCfg_channels (e : S ≃ T) (cfg : Config k Bool S Unit input) :
    (mapCfg e cfg).channels = cfg.channels := rfl

theorem mapCfg_step (e : S ≃ T) (cfg : Config k Bool S Unit input)
    (action : Turing.Action k Bool S) (symbol : Unit → Option Bool)
    (move : Unit → SignType) :
    (mapCfg e cfg).step { action with state := action.state.map e } symbol move =
      mapCfg e (cfg.step action symbol move) := by
  cases cfg
  simp [mapCfg, Turing.MultiTapeMachine.Config.step, Cfg.mapState,
    Turing.Action.apply]

theorem mapCfg_receive (e : S ≃ T) (cfg : Config k Bool S Unit input)
    (next : S) (reply : Word) :
    (mapCfg e cfg).receive () (e next) reply = mapCfg e (cfg.receive () next reply) := by
  cases cfg
  simp [mapCfg, Turing.MultiTapeMachine.Config.receive, Cfg.mapState]

/-- The state-equivalent machine, with transitions looked up through the inverse
bijection and all successor states mapped forward. -/
def reindex {k : ℕ} (M : MultiTapeMachine k Bool S Unit Id) (e : S ≃ T) :
    MultiTapeMachine k Bool T Unit Id where
  initial := e M.initial
  tr state input work answer :=
    match M.tr (e.symm state) input work answer with
    | .step action symbol move => .step { action with state := action.state.map e } symbol move
    | .query oracle next => .query oracle (e next)

@[simp] theorem reindex_initialConfig (M : MultiTapeMachine k Bool S Unit Id) (e : S ≃ T)
    (word : Word) :
    (reindex M e).initialConfig word = mapCfg e (M.initialConfig word) := rfl

/-- Exact correspondence for bounded runs, including the chronological oracle trace. -/
theorem runFrom_reindex (M : MultiTapeMachine k Bool S Unit Id) (e : S ≃ T)
    (L : Language) (fuel : ℕ) (cfg : Config k Bool S Unit input) :
    runFrom (reindex M e) L fuel (mapCfg e cfg) =
      let result := runFrom M L fuel cfg
      (mapCfg e result.1, result.2) := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
      cases hs : cfg.tapes.state with
      | none => simp [runFrom, mapCfg, hs]
      | some state =>
          simp only [runFrom, mapCfg_state, hs, Option.map_some,
            mapCfg_inputSymbol, mapCfg_workTapeSymbols, mapCfg_answerSymbols,
            mapCfg_channels, reindex, Equiv.symm_apply_apply]
          cases ht : M.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
          | step action symbol move =>
              dsimp only
              rw [mapCfg_step]
              exact ih (cfg.step action symbol move)
          | query oracle next =>
              cases oracle
              dsimp only
              rw [mapCfg_receive]
              exact congrArg
                (fun result => (result.1, ((cfg.channels ()).queryBuffer,
                  L (cfg.channels ()).queryBuffer) :: result.2))
                (ih (cfg.receive () next [L (cfg.channels ()).queryBuffer]))

/-- Reindexing preserves the complete standard-input run, with only its final
control state transformed. -/
theorem run_reindex (M : MultiTapeMachine k Bool S Unit Id) (e : S ≃ T)
    (L : Language) (fuel : ℕ) (word : Word) :
    run (reindex M e) L fuel word =
      let result := run M L fuel word
      (mapCfg e result.1, result.2) := by
  simpa only [run, reindex_initialConfig] using
    (runFrom_reindex M e L fuel (M.initialConfig word))

end AverageCaseComplexity.OracleMachine
