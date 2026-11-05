# Two-query completeness: proof skeleton

`AverageCaseComplexity/Completeness/TwoQuery.lean` outlines Itsykson §3,
Theorems 3.1–3.2 and their prerequisites. **It is not proved:** every theorem
has a `sorry` body, and unimplemented executable constructions also have
explicit placeholders. Successful elaboration checks statements and interfaces,
not the truth of these results.

## Dependency map

| Stage | Principal declarations | What remains to implement/prove |
| --- | --- | --- |
| Machine representation | `boundedAnswer`, `boundedSample`, `exactLanguageBit`, `compile_algorithm`, `compile_sampler` | Binary codes for actual finite-control fair-coin machines; bounded universal interpretation; exhaustive coin enumeration; strict polynomial simulation overhead; exact correspondence with existing PPT certificates |
| Tuple representation | `Instance`, `Seed`, `encodeSeed`, `decodeSeed`, `encode`, `decode` | Self-delimiting binary encoding, round trips, length invariance, logarithmic overhead, payload lower bound, and all-ones rejection |
| Complete language | `language`, `instanceBit`, `query_answers_differ_iff` | Threshold truth table and elementary PMF inequalities relating wrong/give-up probabilities to the most frequent Boolean answer |
| Algorithm 3.1 | `reliabilityTest`, `sampler`, `samplerLaw`, `distribution` | Executable independent trials, Chernoff bounds, exact sampler law, fixed output length, and strict PPT certificate |
| Lemma 3.2 | `seed_fiber_mass_lower`, `distribution_mass_lower`, `distribution_mass_upper` | Count the whole seed fiber; combine it with exact bounded sampling and filter acceptance; account for every preimage in the upper bound |
| Lemma 3.1 | `targetProgram`, `targetProgram_correct`, `bad_instances_mass`, `targetProgram_useful`, `avgBPP_of_small_bad_mass` | 80%-majority solver, exhaustive branch when `k ≥ 2^m`, polynomial runtime in unary accuracy, and nested usefulness |
| Theorem 3.1 | `problem_avgBPP`, `distribution_psamp` | Assemble target membership and samplability |
| Source preparation | `amplified_witness`, `CompiledSource`, `compile_source` | Amplify internal error/give-up thresholds to 0.01; specialize accuracy using compact binary code; compile the exact source sampler |
| Two-query machine | `query_efficient`, `reduction`, `reduction_trace`, `reduction_run` | Certify actual query construction and a uniformly halting finite-control machine; exactly two nonadaptive calls; agree-or-give-up reply processing |
| Reduction conditions | `reduction_correct`, `reduction_useful`, `exceptional_mass`, `query_mass_lower`, `reduction_domination`, `reduction_conditions` | Pointwise correctness on source support, exceptional-set bound, polynomial mass ratio, and collision-free query fibers |
| Theorem 3.2 | `errorlesslyReducible`, `complete` | Assemble errorless hardness and target membership |

The intended first implementation step is the binary tuple/machine-code layer.
The source compilation bridge is substantial: machine codes cannot be arbitrary
PMFs, and short code length does not imply polynomial-time code construction.
`CompiledSource` therefore explicitly requires an efficient code constructor as
well as its compactness and semantic correspondence.

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

## Checking the skeleton

```sh
lake env lean AverageCaseComplexity/Completeness/TwoQuery.lean
```

Expected result: no elaboration errors; `sorry` warnings are intentional.
