# Two-query completeness: implementation in progress

`AverageCaseComplexity/Completeness/TwoQuery.lean` develops Itsykson §3,
Theorems 3.1–3.2 and their prerequisites. **Completeness is not yet proved:**
major executable constructions and foundational theorems still have explicit
`sorry` placeholders. The final assembly has a proof body, but its dependencies
still include `sorryAx`; successful elaboration is not a completeness certificate.

## Completed foundational modules

These modules have no placeholders or additional axioms:

- `Completeness/AnswerLaw.lean`: frequent-answer and peak inequalities,
  agreement/give-up identities, and the complete-language truth table's
  three-quarter upper bound on wrong-answer mass.
- `Completeness/TupleEncoding.lean`: executable checked binary codec, both
  directions of seed round trips, canonical instance round trips, injectivity,
  all-ones rejection, length invariance, logarithmic overhead, and payload bounds.
  The decoder's machine-level efficiency proof remains to be supplied.
- `Completeness/EncodingRuntime.lean`: machine-certified self-delimiting length
  headers and seed encoding from certified field constructors, used by the
  source query-construction theorem.
- `Completeness/CompactCode.lean`: checked round-trip decoding of a fixed
  machine header plus a raw binary accuracy suffix, a machine-certified code
  constructor, and the sharp linear bound on the exponential code length.
  This is the representation layer, not yet the compiler's semantic bridge.
- `Completeness/LengthNormalization.lean`: truncation/padding and exact
  preservation of distributions already supported at a fixed length.
- `Completeness/TailBounds.lean`: burn-in estimate, tail monotonicity,
  accepted-fraction estimate, and the binary-word union-tail inequality.
- `Reductions/QueryPreparation.lean`, `SequentialExecution.lean`,
  `QueryProtocol.lean`, `TwoQueryMachine.lean`, and `StateReindex.lean`:
  finite-control query writing with no instruction overhead; exact sequential
  trace semantics and clock padding after genuine halting; a general machine
  for two arbitrary tidily polynomial-time query functions, with a uniform
  polynomial clock and exact agree-or-give-up output for every oracle; and
  exact state reindexing. Packaging this construction into the main reduction
  remains unfinished. `Tests/TwoQueryMachine.lean` guards its axioms.
- `Completeness/SeedMass.lean`: the complete seed-fiber mass lower bound,
  counting all choices of free input and clock bits by an explicit injection;
  includes finite-bind upper/lower bounds used in the sampler mass proofs.
- `Completeness/ThresholdBounds.lean`: independent answer-count upper/lower
  Hoeffding tails and the 90% reliability filter's 95%/85% acceptance bounds.
- `Completeness/MajorityBounds.lean`: the 80% majority law's pointwise correctness
  and give-up bounds, using the complete-language truth table.
- `Completeness/VoteRuntime.lean`: executable repetition and threshold voting,
  exact agreement with the preceding probability laws, and strict PPT
  certificates whenever the base program and repetition count are certified.

`Tests/TwoQueryFoundations.lean` checks that its listed foundational declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`. This does **not** certify
`complete`, whose transitive dependencies still contain placeholders.

## Dependency map

| Stage | Principal declarations | What remains to implement/prove |
| --- | --- | --- |
| Machine representation | `boundedAnswer`, `boundedSample`, `exactLanguageBit`, `compile_algorithm`, `compile_sampler` | Binary codes for actual finite-control fair-coin machines; bounded universal interpretation; exhaustive coin enumeration; strict polynomial simulation overhead; exact correspondence with existing PPT certificates |
| Tuple representation | `Instance`, `Seed`, `encodeSeed`, `decodeSeed`, `encode`, `decode` | Codec, mathematical properties, and encoder runtime implemented; decoder runtime remains |
| Complete language | `language`, `instanceBit`, `query_answers_differ_iff` | Truth table and elementary PMF inequalities proved; executable bounded evaluation remains outstanding |
| Algorithm 3.1 | `reliabilityTest`, `sampler`, `samplerLaw`, `distribution` | Generic trial/voting programs and their bounds are proved; actual bounded-code execution, sampler implementation, semantic agreement, and its PPT certificate remain. Fixed output length follows from the stated sampler law; the ensemble is implemented by normalization |
| Lemma 3.2 | `seed_fiber_mass_lower`, `distribution_mass_lower`, `distribution_mass_upper` | Whole-fiber bound proved without placeholders; sampler lower/upper mass proofs implemented conditional on the outstanding sampler execution and reliability-test interfaces |
| Lemma 3.1 | `targetProgram`, `targetProgram_correct`, `bad_instances_mass`, `targetProgram_useful`, `avgBPP_of_small_bad_mass` | Generic 80%-majority semantics/runtime and bad-instance mass union bound proved; target-specific universal execution, exhaustive branch, branch decision/runtime, and nested usefulness remain |
| Theorem 3.1 | `problem_avgBPP`, `distribution_psamp` | Assembly implemented, conditional on outstanding construction and mass-bound proofs |
| Source preparation | `amplified_witness`, `CompiledSource`, `compile_source` | Amplification and witness assembly implemented; actual compact algorithm and sampler compilation remain |
| Two-query machine | `query_efficient`, `reduction`, `reduction_trace`, `reduction_run` | Query construction certified relative to `CompiledSource`'s code-construction fields; general finite-control two-query construction and state reindexing proved in `Reductions/TwoQueryMachine.lean` and `StateReindex.lean`; instantiation and packaging as `W.reduction` remain |
| Reduction conditions | `reduction_correct`, `reduction_useful`, `exceptional_mass`, `query_mass_lower`, `reduction_domination`, `reduction_conditions` | Proof bodies implemented from the still-unproved machine, compilation, and sampler mass-bound interfaces; no unconditional support assertion added |
| Theorem 3.2 | `errorlesslyReducible`, `complete` | Assembly implemented, but still depends on unproved prerequisites |

## Highest-priority remaining infrastructure

1. Checked raw machine codes and an executable fair-coin universal interpreter,
   with exact bounded semantics and polynomial physical simulation overhead.
   The library's deterministic universal simulator and saved-coin replay are
   building blocks, not yet this interface.
2. Compile actual PPT witnesses and exact samplers into those codes. Make the
   witnesses intrinsically clocked before increasing the execution bound:
   arbitrary extra execution after an original cutoff can change the output law.
3. Connect `CompactCode`'s certified binary-suffix constructor to the universal
   interpreter's semantics. Its linear `2^|M_k|` bound is proved, but constructing
   that word does not by itself implement accuracy specialization of a machine.
   The interpreter must reconstruct unary accuracy within its certified clock.
4. Instantiate `exists_twoQuery_machine` with the two certified query functions,
   reindex its finite state type, and package its uniform clock and execution
   theorem as `CompiledSource.reduction`.
5. Connect the certified filter to universal execution, discharging the sampler
   law and reliability interfaces used by the mass proofs, and implement the
   exact target-solver branch. The exact branch must test
   `k ≥ 2^m` without first allocating a prohibitively large unary `2^m`.

`CompiledSource` requires an efficient code constructor as well as compactness
and semantic correspondence; short code length alone does not imply efficient
code construction.

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

The skeleton includes `queries_supported_outside_exceptional`, not an
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
lake build AverageCaseComplexity.Completeness.VoteRuntime \
  AverageCaseComplexity.Completeness.TupleEncoding \
  AverageCaseComplexity.Completeness.CompactCode \
  AverageCaseComplexity.Completeness.LengthNormalization \
  AverageCaseComplexity.Completeness.SeedMass
lake env lean Tests/TwoQueryAnswerLaw.lean
lake env lean Tests/TwoQueryEncoding.lean
lake env lean Tests/TwoQueryFoundations.lean
lake env lean AverageCaseComplexity/Completeness/TwoQuery.lean
```

The foundational tests must pass without placeholders or added postulates.
CI runs every `Tests/*.lean` file after the library build, including the axiom
whitelist. The final command still emits `sorry` warnings: final theorem
elaboration is not yet a proof of completeness.
