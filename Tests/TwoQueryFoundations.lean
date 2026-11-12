import AverageCaseComplexity.Completeness.VoteRuntime
import AverageCaseComplexity.Completeness.LengthNormalization
import AverageCaseComplexity.Completeness.CompactCode
import Lean

open AverageCaseComplexity AverageCaseComplexity.Completeness.TwoQuery
open Cslib Cslib.Probability Turing.MultiTapeTM

example : reliabilityVote [] = true := rfl
example : reliabilityVote [some false, some true] = false := rfl
example : reliabilityVote [none, none] = false := rfl
example : majorityVote [] = some false := rfl
example : majorityVote [some false, some true] = none := rfl
example : majorityVote [some true, some true] = some true := rfl
example : majorityVote [none, none] = none := rfl

example (n : ℕ) : 0 < tailBound n := tailBound_pos n
example : tailBound 15 ≤ (1 / 100 : ENNReal) := tailBound_le_onePercent (by decide)
example : (2 ^ 3 : ENNReal) * tailBound 3 < (2 ^ 3 : ENNReal)⁻¹ :=
  binary_union_tail_lt (by decide)

example : (normalizeWord 4 [true, false]).toWord = [true, false, false, false] := rfl
example : (normalizeWord 1 [true, false]).toWord = [true] := rfl
example : (normalizeWord 0 [true]).toWord = [] := rfl

example : specializeCode [] ⟨1, by decide⟩ = [false, true] := by decide
example : specializeCode [] ⟨2, by decide⟩ = [false, false, true] := by decide
example : decodeSpecializedCode [false, true, false] = none := by decide
example (header : Word) (k : Accuracy) :
    decodeSpecializedCode (specializeCode header k) = some (header, k) := by simp
example (header : Word) (k : Accuracy) :
    2 ^ (specializeCode header k).length ≤
      2 ^ ((Cslib.Kolmogorov.selfDelimitingCode header).length + 1) * (k.val + 1) :=
  specializeCode_size header k

example (p : PMF Answer) (n : ℕ) (hbad : peak p ≤ (85 / 100 : ENNReal)) :
    reliabilityLaw p (200 * n ^ 2) true ≤ tailBound n :=
  reliabilityLaw_accept_upper_all p n hbad

example (p : PMF Answer) (n : ℕ) (hn : 0 < n)
    (hgood : (95 / 100 : ENNReal) ≤ peak p) :
    1 - tailBound n ≤ reliabilityLaw p (200 * n ^ 2) true :=
  reliabilityLaw_accept_lower p n hn hgood

example (p : PMF Answer) (b : Bool) :
    majorityLaw p (200 * 2 ^ 2) (some (!fallbackBit p b)) < (1 / 4 : ENNReal) :=
  majorityLaw_wrong_lt_quarter p b 2 (by decide)

example (A : PolyTimeRandomizedScheme)
    (count : Word × Accuracy → ℕ)
    (hc : ComputableTidilyInPolyTime count schemeInputEncoding encUnary) :
    IsPPTOn schemeInputEncoding encBool
      (fun a => reliabilityProgram (A.program a) (count a)) :=
  reliabilityProgram_efficient A.efficient hc

example (A : PolyTimeRandomizedScheme)
    (count : Word × Accuracy → ℕ)
    (hc : ComputableTidilyInPolyTime count schemeInputEncoding encUnary) :
    IsPPTOn schemeInputEncoding answerEncoding
      (fun a => majorityProgram (A.program a) (count a)) :=
  majorityProgram_efficient A.efficient hc

-- This test fails if any completed foundational milestone acquires sorryAx
-- or a new postulate. The unfinished final completeness theorem is deliberately
-- not included: its dependencies have not yet all been implemented.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``decodeSeed_encodeSeed, ``decodeSeed_encodeSeed_eq, ``encodeSeed_length_le,
      ``frequentBit_eq_of_small_wrong_and_giveUp, ``peak_gt_of_small_wrong_and_giveUp,
      ``fallbackBit_wrong_le_threeQuarters, ``burnIn_tail, ``binary_union_tail_lt,
      ``fixedLengthLaw_map_toWord, ``selfDelimitingCode_efficient, ``encodeSeed_efficient_with,
      ``decodeSpecializedCode_specializeCode, ``decodeSpecializedCode_sound,
      ``specializeCode_size, ``specializeCode_efficient,
      ``answerCount_upper_tail, ``answerCount_lower_tail,
      ``reliabilityLaw_accept_upper_all, ``reliabilityLaw_accept_lower,
      ``majorityLaw_wrong_lt_quarter, ``majorityLaw_giveUp,
      ``reliabilityProgram_eval, ``majorityProgram_eval,
      ``reliabilityProgram_efficient, ``majorityProgram_efficient] do
    for axiomName in ← Lean.collectAxioms decl do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {decl}"
