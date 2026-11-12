module

public import AverageCaseComplexity.Amplification.Flat.Basic
public import Complexity.Computability.Probabilistic.Repeat
public import Complexity.Computability.Probabilistic.PPT.Composition
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

@[expose] public section

namespace AverageCaseComplexity

open Cslib Cslib.Probability Turing.MultiTapeTM

/-- The number of occurrences of a fixed answer, computed by filtering and taking length. -/
def answerCount (answer : Answer) (answers : List Answer) : ℕ :=
  answers.count answer

/-- A fixed-answer filter and its length are polynomial-time on encoded answer lists. -/
@[fun_prop] theorem answerCount_computable (answer : Answer) :
    ComputableTidilyInPolyTime (answerCount answer) (encList answerEncoding) encUnary := by
  have htest : ComputableTidilyInDegree
      (fun p : Answer × Answer => decide (p.2 = p.1))
      (encPair answerEncoding answerEncoding) encBool 2 0 := by
    exact (ComputableTidilyInDegree.eq answerEncoding).of_enc_eq fun p => by simp [eq_comm]
  have hfilter : ComputableTidilyInDegree
      (fun answers : List Answer => answers.filter fun a => decide (a = answer))
      (encList answerEncoding) (encList answerEncoding) 3 1 := by
    simpa using ComputableTidilyInDegree.filterWith
      (t := fun p : Answer × Answer => decide (p.2 = p.1))
      (par := fun _ : List Answer => answer) (list := id)
      htest (ComputableTidilyInDegree.const answer) (ComputableTidilyInDegree.of_eq fun _ => rfl)
  have hlength := ComputableTidilyInDegree.length answerEncoding
  have hfilterLength := hlength.comp hfilter
  exact hfilterLength.of_enc_eq (fun answers => by
    simp [answerCount, List.count_eq_length_filter, beq_eq_decide]) |>.computableTidilyInPolyTime

/-- Flat three-way plurality is a tidy polynomial-time postprocessing of encoded answers. -/
theorem computableTidilyInPolyTime_plurality :
    ComputableTidilyInPolyTime plurality (encList answerEncoding) answerEncoding := by
  have hnone := answerCount_computable none
  have hfalse := answerCount_computable (some false)
  have htrue := answerCount_computable (some true)
  have hfalseLeNone : ComputableTidilyInPolyTime
      (fun l : List Answer => decide (answerCount (some false) l ≤ answerCount none l))
      (encList answerEncoding) encBool :=
    ComputableTidilyInPolyTime.unary_le' hfalse hnone
  have htrueLeNone : ComputableTidilyInPolyTime
      (fun l : List Answer => decide (answerCount (some true) l ≤ answerCount none l))
      (encList answerEncoding) encBool :=
    ComputableTidilyInPolyTime.unary_le' htrue hnone
  have htrueLeFalse : ComputableTidilyInPolyTime
      (fun l : List Answer => decide (answerCount (some true) l ≤ answerCount (some false) l))
      (encList answerEncoding) encBool :=
    ComputableTidilyInPolyTime.unary_le' htrue hfalse
  have hnoneCondition := ComputableTidilyInPolyTime.decide_and hfalseLeNone htrueLeNone
  have hrest := htrueLeFalse.ite_decide
    (ComputableTidilyInPolyTime.const (encIn := encList answerEncoding)
      (encMid := answerEncoding) (some false))
    (ComputableTidilyInPolyTime.const (encIn := encList answerEncoding)
      (encMid := answerEncoding) (some true))
  have hplurality := hnoneCondition.ite_decide
    (ComputableTidilyInPolyTime.const (encIn := encList answerEncoding)
      (encMid := answerEncoding) none) hrest
  exact hplurality.of_enc_eq fun answers => by
    rfl

/-- Flat repetition using a caller-supplied polynomial-time repetition count. -/
theorem isPPTOn_flatProgram {α : Type} {input : α ↪ Word}
    {program : α → Cslib.ProbComp Answer} {count : α → ℕ}
    (hprogram : IsPPTOn input answerEncoding program)
    (hcount : ComputableTidilyInPolyTime count input encUnary) :
    IsPPTOn input answerEncoding (fun a => flatProgram (program a) (count a)) := by
  have hrep := hprogram.replicate hcount
  have hplurality := computableTidilyInPolyTime_plurality
  have hresult := hrep.map hplurality
  simpa only [flatProgram] using hresult

/-- Flat amplification of an efficient randomized scheme with a computed repetition count. -/
def PolyTimeRandomizedScheme.flatAmplify (A : PolyTimeRandomizedScheme)
    (count : Word × Accuracy → ℕ)
    (hcount : ComputableTidilyInPolyTime count schemeInputEncoding encUnary) :
    PolyTimeRandomizedScheme where
  program a := flatProgram (A.program a) (count a)
  efficient := isPPTOn_flatProgram A.efficient hcount

@[simp] theorem run_flatAmplify (A : PolyTimeRandomizedScheme)
    (count : Word × Accuracy → ℕ)
    (hcount : ComputableTidilyInPolyTime count schemeInputEncoding encUnary)
    (x : Word) (k : Accuracy) :
    (A.flatAmplify count hcount).run x k = flatPMF (A.run x k) (count (x, k)) := by
  simp [PolyTimeRandomizedScheme.flatAmplify, PolyTimeRandomizedScheme.run]

/-- A linear repetition clock proportional to the complete unary scheme-input length. -/
def linearRepeatCount (rate : ℕ) (a : Word × Accuracy) : ℕ :=
  72 * (rate + 1) * ((schemeInputEncoding a).length + 1)

/-- For every fixed rate, the linear repetition clock is polynomial-time computable. -/
theorem linearRepeatCount_efficient (rate : ℕ) :
    ComputableTidilyInPolyTime (linearRepeatCount rate) schemeInputEncoding encUnary := by
  have hlength := ComputableTidilyInPolyTime.encoding_length schemeInputEncoding
  unfold linearRepeatCount
  fun_prop

/-- Flat amplification with the standard linear-in-input-length repetition clock. -/
def PolyTimeRandomizedScheme.flatAmplifyLinear (A : PolyTimeRandomizedScheme) (rate : ℕ) :
    PolyTimeRandomizedScheme :=
  A.flatAmplify (linearRepeatCount rate) (linearRepeatCount_efficient rate)

@[simp] theorem run_flatAmplifyLinear (A : PolyTimeRandomizedScheme) (rate : ℕ)
    (x : Word) (k : Accuracy) :
    (A.flatAmplifyLinear rate).run x k =
      flatPMF (A.run x k) (linearRepeatCount rate (x, k)) := by
  simp [PolyTimeRandomizedScheme.flatAmplifyLinear]

end AverageCaseComplexity
