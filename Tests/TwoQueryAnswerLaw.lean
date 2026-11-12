import AverageCaseComplexity.Completeness.AnswerLaw

open AverageCaseComplexity AverageCaseComplexity.Completeness.TwoQuery

example (b : Bool) : combine b b = some b := combine_self b
example : combine false true = none := by decide
example : combine true false = none := by decide

example (b : Bool) : frequentBit (PMF.pure (some b)) = b := by
  apply frequentBit_eq_of_small_wrong_and_giveUp
  · cases b <;> norm_num [PMF.pure_apply]
  · norm_num [PMF.pure_apply]

example (b : Bool) : (98 / 100 : ENNReal) < peak (PMF.pure (some b)) := by
  apply peak_gt_of_small_wrong_and_giveUp _ b
  · cases b <;> norm_num [PMF.pure_apply]
  · norm_num [PMF.pure_apply]

#print axioms frequentBit_eq_of_small_wrong_and_giveUp
#print axioms peak_gt_of_small_wrong_and_giveUp
#print axioms combine_eq_none_iff
