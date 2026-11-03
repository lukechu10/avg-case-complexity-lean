module

public import AverageCaseComplexity.Amplification.Basic
public import Complexity.Computability.Probabilistic.PPT.Capture

@[expose] public section

namespace AverageCaseComplexity

open Cslib Cslib.Probability Turing.MultiTapeTM

/-- One three-run plurality boost preserves strict polynomial time. -/
theorem isPPTOn_boostProgram {α : Type} {input : α ↪ Word}
    {program : α → Cslib.ProbComp Answer}
    (hprogram : Cslib.Probability.IsPPTOn input answerEncoding program) :
    Cslib.Probability.IsPPTOn input answerEncoding (fun a => boostProgram (program a)) := by
  have htriple : Cslib.Probability.IsPPTOn input
      (encPair answerEncoding (encPair answerEncoding answerEncoding))
      (fun a => do
        let first ← program a
        let second ← program a
        let third ← program a
        pure (first, second, third)) := by
    fun_prop
  have hplurality : ComputableTidilyInPolyTime
      (fun t : Answer × Answer × Answer => plurality3 t.1 t.2.1 t.2.2)
      (encPair answerEncoding (encPair answerEncoding answerEncoding)) answerEncoding :=
    (ComputableTidilyInDegree.of_finite
      (encIn := encPair answerEncoding (encPair answerEncoding answerEncoding))
      (encMid := answerEncoding)
      (fun t : Answer × Answer × Answer => plurality3 t.1 t.2.1 t.2.2)).computableTidilyInPolyTime
  have hresult := htriple.map hplurality
  apply hresult.congr
  intro a
  simp [boostProgram, Cslib.ProbComp.eval_bind, PMF.map, Function.comp_def]

/-- Any fixed number of iterated boosts preserves strict polynomial time. -/
theorem isPPTOn_amplifyProgram {α : Type} {input : α ↪ Word}
    {program : α → Cslib.ProbComp Answer}
    (hprogram : Cslib.Probability.IsPPTOn input answerEncoding program) (depth : ℕ) :
    Cslib.Probability.IsPPTOn input answerEncoding
      (fun a => amplifyProgram (program a) depth) := by
  induction depth with
  | zero => simpa [amplifyProgram] using hprogram
  | succ depth ih =>
      simpa only [amplifyProgram] using isPPTOn_boostProgram ih

/-- A fixed-depth amplification of an efficient randomized scheme. -/
def PolyTimeRandomizedScheme.amplify (A : PolyTimeRandomizedScheme) (depth : ℕ) :
    PolyTimeRandomizedScheme where
  program a := amplifyProgram (A.program a) depth
  efficient := isPPTOn_amplifyProgram A.efficient depth

@[simp] theorem run_amplify (A : PolyTimeRandomizedScheme) (depth : ℕ)
    (x : Word) (k : Accuracy) :
    (A.amplify depth).run x k = amplifyPMF (A.run x k) depth := by
  simp [PolyTimeRandomizedScheme.amplify, PolyTimeRandomizedScheme.run]

end AverageCaseComplexity
