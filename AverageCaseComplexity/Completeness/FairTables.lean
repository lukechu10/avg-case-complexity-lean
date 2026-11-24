module

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Correct
import all Complexity.Computability.Machines.Turing.MultiTape.Universal.Correct

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal

variable {k : ℕ} {S : Type} [Fintype S] (e : S ↪ ℕ) (sym : Bool ↪ ℕ)
  (M : MultiTapePTM k Bool S)

/-- A closed PTM has a finite transition table for each possible value of its fresh bit. -/
noncomputable def coinDesc (b : Bool) : Desc := desc e sym (M.withCoin b).toTM

/-- Interleaving the two universal tables follows the *same* path as replaying the
source machine, not merely a path having the same output distribution. -/
theorem fold_coinDesc (x coins : List Bool) (s : SCfg × List ℕ)
    (cfg : MultiTapeMachine.Config k Bool S Empty x)
    (he : cfg.tapes.map e sym = s.1.toCfg k (x.map sym) s.2)
    (hs : s.1.WellShaped k (x.map sym)) :
    let final := coins.foldl (fun c b => stepOut (coinDesc e sym M b) (x.map sym) c) s
    (M.runClosedConfigFromCoins coins cfg).tapes.map e sym =
      final.1.toCfg k (x.map sym) final.2 := by
  induction coins generalizing cfg s with
  | nil => exact he
  | cons b coins ih =>
    have hstep := toCfg_step (d := coinDesc e sym M b) (out := s.2)
      (tm := (M.withCoin b).toTM.map e sym) hs (fun q hq => by
        rw [← he] at hq ⊢
        obtain ⟨q, -, rfl⟩ := Option.map_eq_some_iff.mp hq
        rw [Cfg.inputSymbol_map]
        exact holds_desc e sym _ q _ cfg.tapes.workTapeSymbols)
    apply ih _ _ _ hstep.2
    rw [MultiTapeMachine.step_toTM, ← step_map, he]
    exact hstep.1.symm

/-- Output equality from blank tapes, for every saved sequence of fair coins. -/
theorem run_coinDesc (x coins : List Bool) :
    (M.runClosedCoins coins x).map sym =
      (coins.foldl (fun c b => stepOut (coinDesc e sym M b) (x.map sym) c)
        (init (coinDesc e sym M false), [])).2 := by
  have hi := toCfg_init (k := k) (d := coinDesc e sym M false) (x := x.map sym) rfl
  have h := fold_coinDesc e sym M x coins (init (coinDesc e sym M false), []) (M.initialConfig x)
    (by dsimp only; rw [hi.1]; exact Cfg.map_init ..) hi.2
  exact congrArg Cfg.output h

end AverageCaseComplexity.Completeness.TwoQuery
