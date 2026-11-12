module

public import AverageCaseComplexity.Reductions.QueryPreparation
public import AverageCaseComplexity.Reductions.SequentialExecution
public import AverageCaseComplexity.Completeness.AnswerLaw

@[expose] public section

namespace AverageCaseComplexity.OracleMachine

open Turing Turing.MultiTapeMachine

variable {k : ℕ} {input : Word}

/-- A local instruction which changes only control and (optionally) output. -/
def controlAction {State : Type} (next : Option State) (out : Option Bool := none) :
    Turing.Action k Bool State := ⟨0, fun _ => (none, 0), out, next⟩

/-- Submit the current buffer and halt in two instructions, retaining the reply
for the next phase to read. No query word is built into this machine. -/
def ask : MultiTapeMachine k Bool Bool Unit Id where
  initial := false
  tr state _ _ _ := if state then
    .step (controlAction none) (fun _ => none) (fun _ => 0)
    else .query () true

/-- The common tape/channel result of a query, with a chosen final control state. -/
def queried {S T : Type} (cfg : Config k Bool S Unit input) (L : Language)
    (next : Option T) : Config k Bool T Unit input where
  tapes := cfg.tapes.withState next
  channels _ := ⟨[], [L (cfg.channels ()).queryBuffer], 0⟩

/-- Exact accounting for the first submission, including its two instructions. -/
theorem runFrom_ask (L : Language) (cfg : Config k Bool Bool Unit input)
    (h : cfg.tapes.state = some false) :
    runFrom ask L 2 cfg =
      (queried cfg L (none : Option Bool),
        [((cfg.channels ()).queryBuffer, L (cfg.channels ()).queryBuffer)]) := by
  simp only [runFrom, h, ask, Bool.false_eq_true, ite_false]
  simp [Config.receive, Config.step, controlAction, Turing.Action.apply,
    queried, Cfg.withState]

/-- Submit the second query, remember the preceding reply in finite control,
and emit the two-bit agree-or-give-up answer in three instructions. -/
def agree : MultiTapeMachine k Bool (Option Bool ⊕ Bool) Unit Id where
  initial := .inl none
  tr state _ _ answer := match state with
    | .inl none => .query () (.inl (some ((answer ()).getD false)))
    | .inl (some first) =>
        let second := (answer ()).getD false
        .step (controlAction (some (.inr (if first = second then first else false)))
          (some (decide (first = second)))) (fun _ => none) (fun _ => 0)
    | .inr bit => .step (controlAction none (some bit)) (fun _ => none) (fun _ => 0)

/-- Exact terminal answer, for arbitrary query words rather than fixed queries. -/
theorem runFrom_agree (L : Language) (cfg : Config k Bool (Option Bool ⊕ Bool) Unit input)
    (first : Bool) (hstate : cfg.tapes.state = some (.inl none))
    (hanswer : cfg.answerSymbols () = some first) :
    runFrom agree L 3 cfg =
      ({ queried cfg L (none : Option (Option Bool ⊕ Bool)) with
          tapes := { cfg.tapes.withState none with
            output := cfg.tapes.output ++ answerEncoding
              (Completeness.TwoQuery.combine first (L (cfg.channels ()).queryBuffer)) } },
        [((cfg.channels ()).queryBuffer, L (cfg.channels ()).queryBuffer)]) := by
  simp only [runFrom, hstate, agree, hanswer, Option.getD_some]
  simp [Config.receive, Config.step, controlAction, Turing.Action.apply,
    queried, Cfg.withState, Config.answerSymbols, Channel.answerSymbol,
    Completeness.TwoQuery.combine, answerEncoding]
  by_cases he : first = L (cfg.channels ()).queryBuffer <;> simp [he]

end AverageCaseComplexity.OracleMachine
