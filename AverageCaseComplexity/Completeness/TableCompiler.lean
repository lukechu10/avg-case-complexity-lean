module

public import AverageCaseComplexity.Completeness.FairTables
public import AverageCaseComplexity.Completeness.SourceReplay

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery

open Turing Turing.MultiTapeTM.Universal

private def sym : Bool ↪ ℕ := ⟨fun b => if b then 1 else 0, by decide⟩

private theorem coinDesc_shape {t : ℕ} {S : Type} [Fintype S]
    (e : S ↪ ℕ) (M : MultiTapePTM t Bool S) (b : Bool) :
    ∀ row ∈ (coinDesc e sym M b).table, RawRowShape t row := by
  intro row hr
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hr
  simp [RawRowShape, key, Act.ofAction]

/-- Serialize both finite transition tables, once and for all, preserving each
individual coin-tape execution of the source machine. -/
theorem rawCompiler_correct : RawCompilerCorrect := by
  classical
  intro t S _ M
  let _ := Fintype.ofFinite S
  let e := (Fintype.equivFin S).toEmbedding.trans Fin.valEmbedding
  let df := coinDesc e sym M false
  let dt := coinDesc e sym M true
  let m : RawFairMachine := ⟨t, e M.initial, 0, 1, df.table, dt.table⟩
  refine ⟨encodeRawPair df dt 0 1, m, ?_, (by change 1 ≠ 0; decide), ?_⟩
  · -- The code stores rows in lookup order, without re-numbering states.
    apply decodeRawFairMachine_encodeRawPair <;> first | rfl | decide | apply coinDesc_shape
  · intro x coins
    have hfun : (fun (c : SCfg × List ℕ) (b : Bool) => stepOut
          (if b then (⟨m.tapes, m.initial, m.trueTable⟩ : Desc)
            else ⟨m.tapes, m.initial, m.falseTable⟩) (x.map sym) c) =
        (fun c b => stepOut (coinDesc e sym M b) (x.map sym) c) := by
      funext c b; cases b <;> rfl
    change (coins.foldl _ (init _, [])).2 = (M.runClosedCoins coins x).map sym
    rw [show (fun (c : SCfg × List ℕ) (b : Bool) => stepOut _ (rawInputSymbols m x) c) = _ from hfun]
    exact (run_coinDesc e sym M x coins).symm

end AverageCaseComplexity.Completeness.TwoQuery
