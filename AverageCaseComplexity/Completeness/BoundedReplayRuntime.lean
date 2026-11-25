module

public import AverageCaseComplexity.Completeness.CompactInputRuntime
public import AverageCaseComplexity.Completeness.RawMachineRuntime
public import AverageCaseComplexity.Completeness.RawRowRuntime
public import AverageCaseComplexity.Completeness.ReplayCertificates

@[expose] public section

namespace AverageCaseComplexity.Completeness.TwoQuery
open Turing.MultiTapeTM

theorem replayAnswer_efficient : ComputableTidilyInPolyTime
    (fun p : Word × Word × Word => replayAnswer p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) answerEncoding := by
  apply replayAnswer_efficient_of_decoders runStructuredTables_efficient
    (decodeRawFairMachine_efficient decodeRawRow_efficient)
  exact compactInputRuntime_efficient.of_enc_eq (fun p => congrArg _ (compactInputRuntime_eq ..).symm)

theorem replaySample_efficient : ComputableTidilyInPolyTime
    (fun p : Word × ℕ × Word => (replaySample p.1 p.2.1 p.2.2).toWord)
    (encPair encBits (encPair encUnary encBits)) encBits :=
  replaySample_efficient_of_decoder runStructuredTables_efficient
    (decodeRawFairMachine_efficient decodeRawRow_efficient)

end AverageCaseComplexity.Completeness.TwoQuery
