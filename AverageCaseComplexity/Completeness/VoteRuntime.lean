module

public import AverageCaseComplexity.Completeness.MajorityBounds
public import AverageCaseComplexity.Amplification.Flat.Runtime

@[expose] public section

/-! # Machine-certified repetition and threshold voting

The base computation is a real probabilistic program with a PPT certificate.
The repetition count and all vote-counting operations are machine-certified;
no real-valued probability comparison is performed by these algorithms.
-/

namespace AverageCaseComplexity.Completeness.TwoQuery

open Cslib Cslib.Probability Turing.MultiTapeTM

/-- Integer 90%-threshold test on a list of sampled answers. -/
def reliabilityVote (answers : List Answer) : Bool :=
  decide (9 * answers.length ≤ 10 * answers.count (some false) ∨
    9 * answers.length ≤ 10 * answers.count (some true))

/-- Integer 80%-majority decision on a list of sampled answers. -/
def majorityVote (answers : List Answer) : Answer :=
  if 4 * answers.length ≤ 5 * answers.count (some false) then some false
  else if 4 * answers.length ≤ 5 * answers.count (some true) then some true
  else none

theorem list_count_ofFn {N : ℕ} (outcome : Fin N → Answer) (a : Answer) :
    (List.ofFn outcome).count a = answerCount a outcome := by
  classical
  induction N with
  | zero => simp [answerCount]
  | succ N ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.count_append,
      List.count_singleton]
    unfold answerCount
    rw [Fin.sum_univ_castSucc]
    simpa only [beq_iff_eq, Bool.decide_eq_true, List.ofFn, answerCount] using
      congrArg (fun x : ℕ => x + if outcome (Fin.last N) == a then 1 else 0)
        (ih (fun i => outcome i.castSucc))

@[simp] theorem reliabilityVote_ofFn {N : ℕ} (outcome : Fin N → Answer) :
    reliabilityVote (List.ofFn outcome) =
      decide (9 * N ≤ 10 * answerCount (some false) outcome ∨
        9 * N ≤ 10 * answerCount (some true) outcome) := by
  simp [reliabilityVote, list_count_ofFn]

@[simp] theorem majorityVote_ofFn {N : ℕ} (outcome : Fin N → Answer) :
    majorityVote (List.ofFn outcome) = majorityAnswer outcome := by
  simp [majorityVote, majorityAnswer, list_count_ofFn]

/-- The reliability filter is genuine polynomial-time deterministic
postprocessing of the explicitly encoded list. -/
theorem reliabilityVote_efficient :
    ComputableTidilyInPolyTime reliabilityVote (encList answerEncoding) encBool := by
  have hlength := (ComputableTidilyInDegree.length answerEncoding).computableTidilyInPolyTime
  have hfalse := AverageCaseComplexity.answerCount_computable (some false)
  have htrue := AverageCaseComplexity.answerCount_computable (some true)
  have hleft : ComputableTidilyInPolyTime (fun l : List Answer => 9 * l.length)
      (encList answerEncoding) encUnary := by fun_prop
  have hrightFalse : ComputableTidilyInPolyTime
      (fun l : List Answer => 10 * l.count (some false)) (encList answerEncoding) encUnary := by
    change ComputableTidilyInPolyTime
      (fun l => 10 * AverageCaseComplexity.answerCount (some false) l) _ _
    fun_prop
  have hrightTrue : ComputableTidilyInPolyTime
      (fun l : List Answer => 10 * l.count (some true)) (encList answerEncoding) encUnary := by
    change ComputableTidilyInPolyTime
      (fun l => 10 * AverageCaseComplexity.answerCount (some true) l) _ _
    fun_prop
  exact (ComputableTidilyInPolyTime.unary_le' hleft hrightFalse).decide_or
    (ComputableTidilyInPolyTime.unary_le' hleft hrightTrue)

/-- Likewise, the majority solver's threshold comparison and answer selection
have deterministic tidy-machine certificates. -/
theorem majorityVote_efficient :
    ComputableTidilyInPolyTime majorityVote (encList answerEncoding) answerEncoding := by
  have hlength := (ComputableTidilyInDegree.length answerEncoding).computableTidilyInPolyTime
  have hfalse := AverageCaseComplexity.answerCount_computable (some false)
  have htrue := AverageCaseComplexity.answerCount_computable (some true)
  have hleft : ComputableTidilyInPolyTime (fun l : List Answer => 4 * l.length)
      (encList answerEncoding) encUnary := by fun_prop
  have hrightFalse : ComputableTidilyInPolyTime
      (fun l : List Answer => 5 * l.count (some false)) (encList answerEncoding) encUnary := by
    change ComputableTidilyInPolyTime
      (fun l => 5 * AverageCaseComplexity.answerCount (some false) l) _ _
    fun_prop
  have hrightTrue : ComputableTidilyInPolyTime
      (fun l : List Answer => 5 * l.count (some true)) (encList answerEncoding) encUnary := by
    change ComputableTidilyInPolyTime
      (fun l => 5 * AverageCaseComplexity.answerCount (some true) l) _ _
    fun_prop
  have hfalseTest := ComputableTidilyInPolyTime.unary_le' hleft hrightFalse
  have htrueTest := ComputableTidilyInPolyTime.unary_le' hleft hrightTrue
  exact hfalseTest.ite_decide (ComputableTidilyInPolyTime.const (some false))
    (htrueTest.ite_decide (ComputableTidilyInPolyTime.const (some true))
      (ComputableTidilyInPolyTime.const none))

def reliabilityProgram (program : ProbComp Answer) (N : ℕ) : ProbComp Bool :=
  reliabilityVote <$> OracleComp.replicate N program

def majorityProgram (program : ProbComp Answer) (N : ℕ) : ProbComp Answer :=
  majorityVote <$> OracleComp.replicate N program

@[simp] theorem reliabilityProgram_eval (program : ProbComp Answer) (N : ℕ) :
    ProbComp.eval (reliabilityProgram program N) = reliabilityLaw (ProbComp.eval program) N := by
  simp only [reliabilityProgram, ProbComp.eval_map, ProbComp.eval_replicate, PMF.map_comp]
  unfold reliabilityLaw
  congr 1
  funext outcome
  exact reliabilityVote_ofFn outcome

@[simp] theorem majorityProgram_eval (program : ProbComp Answer) (N : ℕ) :
    ProbComp.eval (majorityProgram program N) = majorityLaw (ProbComp.eval program) N := by
  simp only [majorityProgram, ProbComp.eval_map, ProbComp.eval_replicate, PMF.map_comp]
  unfold majorityLaw
  congr 1
  funext outcome
  exact majorityVote_ofFn outcome

theorem reliabilityProgram_efficient {α : Type} {input : α ↪ Word}
    {program : α → ProbComp Answer} {count : α → ℕ}
    (hprogram : IsPPTOn input answerEncoding program)
    (hcount : ComputableTidilyInPolyTime count input encUnary) :
    IsPPTOn input encBool (fun a => reliabilityProgram (program a) (count a)) :=
  (hprogram.replicate hcount).map reliabilityVote_efficient

theorem majorityProgram_efficient {α : Type} {input : α ↪ Word}
    {program : α → ProbComp Answer} {count : α → ℕ}
    (hprogram : IsPPTOn input answerEncoding program)
    (hcount : ComputableTidilyInPolyTime count input encUnary) :
    IsPPTOn input answerEncoding (fun a => majorityProgram (program a) (count a)) :=
  (hprogram.replicate hcount).map majorityVote_efficient

end AverageCaseComplexity.Completeness.TwoQuery
