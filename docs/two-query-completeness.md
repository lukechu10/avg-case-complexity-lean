# Two-query completeness

`AverageCaseComplexity.Completeness.TwoQuery.complete` formalizes Itsykson §3, Theorems 3.1–3.2. The constructed problem belongs to `WithPSamp AvgBPP`, and every member of that class has an errorless reduction to it using two nonadaptive queries.

## Proof map

- **Complete language:** `TupleEncoding` represents an instance with logarithmic overhead. `BoundedMachine` parses finite transition tables and replays one step per supplied coin. `FairReplay` proves that exhaustive integer counting on finite tapes gives exactly the PMF decision, including the one-quarter boundary and Boolean tie. `AnswerLaw` gives the pointwise wrong-answer bound.
- **Samplable ensemble (Algorithm 3.1):** `sampler` draws a uniform seed, runs the bounded length-normalized sampler, tests reliability, and emits the tuple or an all-ones word. `sampler_eval` proves its law, and `sampler_output_length` proves it has the requested length even on malformed seeds. The seed-fiber bound in `SeedMass` and the independent-trial tail bounds in `ThresholdBounds` give both point-mass estimates in Lemma 3.2.
- **Target solver (Lemma 3.1):** `targetProgram` rejects invalid inputs, enumerates all coin tapes if the unary accuracy can pay for them, and otherwise uses the 80% majority scheme. `targetProgram_correct` and `targetProgram_useful` are unconditional. `ExactVoteRuntime` certifies guarded doubling enumeration, proves each tape occurs exactly once, and charges intermediate lists to the input size. `VoteRuntime` supplies certified repetition and voting.
- **Source compilation:** `SourceClock` turns a PPT cutoff into a genuine halting bound so padding cannot change the distribution. `FairTables` proves replay of both transition tables agrees with every source coin tape. `TableCompiler` serializes those tables and proves the raw compiler correct; `SourceReplay` handles compact specialization and normalization. Both `compile_algorithm` and `compile_sampler` are proved without placeholders.
- **Two-query reduction:** `CompiledSource.reduction` packages the finite-control machine for two certified query constructors. Its trace is exactly the two prescribed queries for every oracle; its answer is their agreement or give-up. The correctness, usefulness and domination proofs use the source law and the sampler mass bounds.
- **Runtime:** `TupleDecodingRuntime` certifies seed and instance decoding on arbitrary words. `RawDecoderRuntime` certifies unary field scanning. `UniversalStepRuntime` certifies a single step even on an unreachable configuration by bounding the input index before converting it to unary. `RawRowRuntime` and `RawMachineRuntime` certify checked table parsing, `FairTableRuntime` bounds the whole coin-driven simulation, and `BoundedReplayRuntime` supplies the replay certificates used by `sampler_efficient` and `targetProgram_efficient`.

`Tests/TwoQueryExecution.lean` guards the completed execution and compilation milestones against additional axioms; `Tests/BoundedReplay.lean` exercises them on an actual two-state machine with distinct nonstandard symbol codes.

## Conventions and deliberate adjustments

- Accuracy is `k : Accuracy`, requesting error less than `1/k`. Runtime and
  domination use `n+k+2`, consistently with existing reduction definitions.
- The source clock includes `|x| + burnIn + 1`, ensuring the strict validity
  condition even at length zero.
- Malformed and invalid target tuples are rejected deterministically.
- Bounded sampler outputs are truncated/padded to the requested length. This
  preserves genuine source samplers and makes Algorithm 3.1 length-preserving
  even for arbitrary encoded machines. Encoding length must depend only on
  field lengths for this argument to work.
- A logarithmic-overhead encoding is required, but byte-for-byte agreement with
  Remark 3.1 is not. The mass lower bound uses the weaker integer denominator
  `2^20 * (N+1)^10 * 2^(|M|+|S|)` rather than the printed logarithmic prefactor.
  Compact accuracy specialization must keep `2^|M_k|` polynomial in `k`.
- `reduction_trace` is stated for **every** Boolean oracle, so nonadaptivity is
  explicit. `PolyTimeOracleScheme` separately enforces uniform polynomial
  halting and valid output encoding; two calls or short queries alone do not
  supply those certificates.

## Support qualification

The proof establishes `queries_supported_outside_exceptional`, not an
unconditional `QueriesSupported` theorem. Lemma 3.2's lower bound applies to
reliable source computations outside the exceptional set. A computation that
always gives up need not pass the sampler's reliability filter at all.

Thus Theorem 3.2 is stated using the existing `ErrorlesslyReducible` relation.
It does not silently strengthen that relation or resolve the separate support
issue in `docs/section2-closure.md`. Any later use of errorless `AvgP` closure
must retain its additional support/global-correctness hypothesis, or separately
modify the construction and prove the stronger property.

## Validation

```sh
lake build
lake env lean Tests/TwoQueryExecution.lean
lake env lean Tests/BoundedReplay.lean
```

CI runs every `Tests/*.lean` file. `TwoQueryExecution.lean` checks the transitive axioms of `complete` against the whitelist `propext`, `Classical.choice`, and `Quot.sound`.
