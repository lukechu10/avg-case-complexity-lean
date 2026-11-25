import AverageCaseComplexity.Completeness.TwoQuery

open AverageCaseComplexity AverageCaseComplexity.Completeness.TwoQuery
open Turing.MultiTapeTM.Universal

/- Two-state source with no work tapes. Both tables emit the answer tag first;
then the second transition emits the selected coin. Use nonstandard symbol
numbers to exercise both input and output translation. -/
private def table (bit : Bool) : Desc :=
  ⟨0, 0, [(⟨0, some 5, []⟩, ⟨0, [], some 5, some 1⟩),
          (⟨1, some 5, []⟩, ⟨0, [], some (if bit then 5 else 3), none⟩)]⟩

private def header := encodeRawPair (table false) (table true) 3 5
private def code := specializeCode header ⟨1, by decide⟩

#guard replayAnswer code [] [] == none
#guard replayAnswer code [] [true] == none
#guard replayAnswer code [] [true, false] == some false
#guard replayAnswer code [] [false, true] == some true
#guard replayAnswer code [] [false, true, false] == some true
-- A tie between the two Boolean answers goes to false, regardless of fallback.
#guard exactLanguageBit code 2 [] true == false
-- If the tape ends after the tag, every run gives up and C uses its fallback.
#guard exactLanguageBit code 1 [] true == true
-- A raw sampler receives unary length, and short output is padded on the right.
#guard (replaySample header 3 [true, false]).toWord == [true, false, false]
