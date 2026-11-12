module

public import AverageCaseComplexity.Reductions.OracleMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Sequential

@[expose] public section

namespace AverageCaseComplexity.OracleMachine

open Turing Turing.MultiTapeMachine

variable {k : ℕ} {S T : Type} {input : Word}

@[simp] theorem right_state (cfg : Config k Bool T Unit input) :
    (Sequential.right (State₀ := S) cfg).tapes.state = cfg.tapes.state.map Sum.inr := rfl

@[simp] theorem right_inputSymbol (cfg : Config k Bool T Unit input) :
    (Sequential.right (State₀ := S) cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem right_workSymbols (cfg : Config k Bool T Unit input) :
    (Sequential.right (State₀ := S) cfg).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem right_answerSymbols (cfg : Config k Bool T Unit input) :
    (Sequential.right (State₀ := S) cfg).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem right_channels (cfg : Config k Bool T Unit input) :
    (Sequential.right (State₀ := S) cfg).channels = cfg.channels := rfl

@[simp] theorem right_step (cfg : Config k Bool T Unit input)
    (a : Turing.Action k Bool T) (symbol : Unit → Option Bool) (move : Unit → SignType) :
    (Sequential.right (State₀ := S) cfg).step { a with state := a.state.map Sum.inr } symbol move =
      Sequential.right (cfg.step a symbol move) := rfl

@[simp] theorem right_receive (cfg : Config k Bool T Unit input) (next : T) (reply : Word) :
    (Sequential.right (State₀ := S) cfg).receive () (Sum.inr next) reply =
      Sequential.right (cfg.receive () next reply) := rfl

/-- Once control has passed to the second phase, both its tape behavior and
chronological trace are unchanged by sequential embedding. -/
theorem runFrom_seq_right
    (first : MultiTapeMachine k Bool S Unit Id)
    (second : MultiTapeMachine k Bool T Unit Id) (L : Language)
    (fuel : ℕ) (cfg : Config k Bool T Unit input) :
    runFrom (first.seq second) L fuel (Sequential.right cfg) =
      let result := runFrom second L fuel cfg
      (Sequential.right result.1, result.2) := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
      cases hs : cfg.tapes.state with
      | none => simp [runFrom, hs]
      | some state =>
          cases ht : second.tr state cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
          | step a symbol move =>
              simpa only [runFrom, right_state, hs, Option.map_some, right_inputSymbol,
                right_workSymbols, right_answerSymbols, MultiTapeMachine.seq, Functor.map,
                ht, Sequential.rightAction, right_step] using ih (cfg.step a symbol move)
          | query oracle next =>
              cases oracle
              simpa only [runFrom, right_state, hs, Option.map_some, right_inputSymbol,
                right_workSymbols, right_answerSymbols, MultiTapeMachine.seq, Functor.map,
                ht, Sequential.rightAction, right_receive, right_channels, Prod.fst, Prod.snd] using congrArg
                (fun result => (result.1, ((cfg.channels ()).queryBuffer,
                  L (cfg.channels ()).queryBuffer) :: result.2))
                (ih (cfg.receive () next [L (cfg.channels ()).queryBuffer]))

@[simp] theorem left_state (second : MultiTapeMachine k Bool T Unit Id)
    (cfg : Config k Bool S Unit input) :
    (Sequential.left second cfg).tapes.state =
      some (cfg.tapes.state.elim (Sum.inr second.initial) Sum.inl) := rfl

@[simp] theorem left_inputSymbol (second : MultiTapeMachine k Bool T Unit Id)
    (cfg : Config k Bool S Unit input) :
    (Sequential.left second cfg).tapes.inputSymbol = cfg.tapes.inputSymbol := rfl

@[simp] theorem left_workSymbols (second : MultiTapeMachine k Bool T Unit Id)
    (cfg : Config k Bool S Unit input) :
    (Sequential.left second cfg).tapes.workTapeSymbols = cfg.tapes.workTapeSymbols := rfl

@[simp] theorem left_answerSymbols (second : MultiTapeMachine k Bool T Unit Id)
    (cfg : Config k Bool S Unit input) :
    (Sequential.left second cfg).answerSymbols = cfg.answerSymbols := rfl

@[simp] theorem left_channels (second : MultiTapeMachine k Bool T Unit Id)
    (cfg : Config k Bool S Unit input) :
    (Sequential.left second cfg).channels = cfg.channels := rfl

@[simp] theorem left_step (second : MultiTapeMachine k Bool T Unit Id)
    (cfg : Config k Bool S Unit input) (a : Turing.Action k Bool S)
    (symbol : Unit → Option Bool) (move : Unit → SignType) :
    (Sequential.left second cfg).step
      { a with state := some (a.state.elim (Sum.inr second.initial) Sum.inl) } symbol move =
      Sequential.left second (cfg.step a symbol move) := rfl

@[simp] theorem left_receive (second : MultiTapeMachine k Bool T Unit Id)
    (cfg : Config k Bool S Unit input) (next : S) (reply : Word) :
    (Sequential.left second cfg).receive () (Sum.inl next) reply =
      Sequential.left second (cfg.receive () next reply) := rfl

/-- Exact deterministic sequencing, retaining every tape and every query.
Halting bounds add, including when the first phase halts before its bound. -/
theorem runFrom_seq
    (first : MultiTapeMachine k Bool S Unit Id)
    (second : MultiTapeMachine k Bool T Unit Id) (L : Language)
    (firstTime secondTime : ℕ) (cfg : Config k Bool S Unit input)
    (hfirst : (runFrom first L firstTime cfg).1.tapes.state = none)
    (hsecond : (runFrom second L secondTime
      (Sequential.start second (runFrom first L firstTime cfg).1)).1.tapes.state = none) :
    runFrom (first.seq second) L (firstTime + secondTime) (Sequential.left second cfg) =
      let mid := runFrom first L firstTime cfg
      let final := runFrom second L secondTime (Sequential.start second mid.1)
      (Sequential.right final.1, mid.2 ++ final.2) := by
  induction firstTime generalizing cfg with
  | zero =>
      rw [Sequential.left_halted second cfg hfirst, Nat.zero_add, runFrom_seq_right]
      rfl
  | succ firstTime ih =>
      by_cases hhalt : cfg.tapes.state = none
      · simp only [runFrom_halted first L _ cfg hhalt, Prod.fst, Prod.snd,
          List.nil_append] at hsecond ⊢
        rw [Sequential.left_halted second cfg hhalt, runFrom_seq_right]
        rw [runFrom_eq_of_halted second L secondTime (firstTime + 1 + secondTime)
          (Sequential.start second cfg) (by omega) hsecond]
      · cases hs : cfg.tapes.state with
        | none => exact (hhalt hs).elim
        | some q =>
            cases ht : first.tr q cfg.tapes.inputSymbol cfg.tapes.workTapeSymbols cfg.answerSymbols with
            | step a symbol move =>
                simp only [runFrom, hs, ht] at hfirst hsecond
                simpa only [Nat.succ_add, runFrom, left_state, hs, Option.elim_some,
                  left_inputSymbol, left_workSymbols, left_answerSymbols, MultiTapeMachine.seq,
                  Functor.map, ht, Sequential.leftAction, left_step] using
                  ih (cfg.step a symbol move) hfirst hsecond
            | query oracle next =>
                cases oracle
                simp only [runFrom, hs, ht, Prod.fst] at hfirst hsecond
                simpa only [Nat.succ_add, runFrom, left_state, hs, Option.elim_some,
                  left_inputSymbol, left_workSymbols, left_answerSymbols, MultiTapeMachine.seq,
                  Functor.map, ht, Sequential.leftAction, left_receive, left_channels,
                  Prod.fst, Prod.snd, List.cons_append] using congrArg
                    (fun result => (result.1, ((cfg.channels ()).queryBuffer,
                      L (cfg.channels ()).queryBuffer) :: result.2))
                    (ih (cfg.receive () next [L (cfg.channels ()).queryBuffer]) hfirst hsecond)

end AverageCaseComplexity.OracleMachine
