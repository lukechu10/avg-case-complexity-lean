# Lean foundations for Itsykson Section 2

## Implemented modules

All definitions live in namespace `AverageCaseComplexity`.

| Module | Contents |
| --- | --- |
| `Basic` | `Word = List Bool`, `FixedWord n = Fin n → Bool`, `Language`, `Answer = Option Bool`, `Accuracy`, `IsAllowed` |
| `Accuracy` | Reciprocal error bounds, rational approximation, injective unary scheme-input encoding and size bounds |
| `Distributions` | `Ensemble`, finite `eventProb`, ensemble event probabilities and support, `DistributionalProblem`, `uniformEnsemble` |
| `Schemes` | Deterministic/randomized semantic schemes; correctness, usefulness, and heuristic conditions; a probability-level deterministic inclusion theorem |
| `Sampling` | Unary input embedding, word-valued ensemble semantics, machine-certified exact `PSamp` |
| `Classes` | Machine-certified deterministic/randomized schemes; `AvgP`, `AvgBPP`, `HeurP`, `HeurBPP`; class inclusions and `WithPSamp` |
| `Amplification` | Constant-error amplification, general threshold conversions, and `AvgBPP.toHeurBPP` |
| `Amplification.Exponential` | Flat plurality, Hoeffding tail, certified polynomial-time exponential-error amplification, and an equivalent characterization of `AvgBPP` |

We explicitly extend the paper's positive-length ensembles to length zero.
`Accuracy` is now a positive natural number `k`, requesting error less than
`1/k`. The former rational type is retained as `RationalAccuracy` for
comparison with the paper. `schemeInputEncoding` represents `(x,k)` as
`1^k 0 x`; this is injective and has length `|x| + k + 1`.
Event probabilities use `ENNReal`, matching Mathlib's `PMF` API; thus `1 / 4`
is interpreted as extended-nonnegative-real division, not natural division.
`Accuracy.bound` is the extended-nonnegative-real reciprocal of `k`.

## Reused computational APIs

The dependency is the pinned `complexitylib2` package, with `Complexity.*`
imports and `Cslib` / `Turing` namespaces.

- `Complexity.Languages.Probabilistic.Basic` supplies `Cslib.ProbComp` and
  `ProbComp.eval : ProbComp α → PMF α`. This gives executable probabilistic
  programs and their distributions, but no efficiency assertion on its own.
- `Complexity.Computability.Probabilistic.PPT` supplies
  `Cslib.Probability.IsPPTOn inputEncoding outputEncoding program`.
  One finite-control fair-coin multitape machine and one clock
  `c * (encodedInputLength + 1)^d` must realize the encoded output law for
  every input. The clock is a worst-case cutoff, not an expectation.
- `Sampling.PSamp` uses precisely this certificate, a unary encoding of `n`,
  and identity encoding of output words. Its equality of PMFs also enforces
  that the sampler returns exactly `n` bits.
- `Complexity.Computability.Probabilistic.PPT.Clock` provides conversion
  from cutoff semantics to an intrinsically halting polynomial-time machine
  if we need explicit halting witnesses later.
- Deterministic computation can reuse
  `Turing.MultiTapeTM.ComputableTidilyInPolyTime` from
  `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime`.
- Future oracle reductions can use `ProbOracleComp` / `WordOracleComp` and
  the oracle machine APIs in `Complexity.Computability.Probabilistic.Oracle`.
  Their exact deterministic specialization and query trace interface still
  need to be selected when implementing Definition 2.2.

Do not use `Cslib.TimeM` alone as a machine-efficiency certificate: it adds
user-specified costs rather than verifying execution time.

## Scope and next step

`Schemes` separates probability properties from executable implementations.
An arbitrary `Word → Accuracy → PMF Answer` is **not** an efficient scheme.
`Classes` now combines those semantic conditions with machine certificates:

- `PolyTimeDeterministicScheme` certifies the curried `run` function via
  `ComputableTidilyInPolyTime` on `(x,k)`.
- `PolyTimeRandomizedScheme` certifies a `ProbComp Answer` program via
  `IsPPTOn`. Its `run` is the PMF semantics of that program.
- Both use `schemeInputEncoding` and a fixed two-bit answer encoding:
  `00` for giving up, `10` for false, `11` for true. These are explicit
  implementation choices, not the output convention used later in Section 3.
- `AvgP`, `AvgBPP`, `HeurP`, and `HeurBPP` existentially quantify over
  these certified schemes and impose the corresponding semantic conditions.
- `WithPSamp C P` is the restriction `C P ∧ PSamp P.distribution`.

Proved inclusions: `AvgP.toHeurP`, `AvgP.toAvgBPP`, `HeurP.toHeurBPP`,
and `AvgBPP.toHeurBPP` (the last in `Amplification`).
`WithPSamp.mono` transfers any inclusion to samplable ensembles.
`AvgP.constant` constructs a machine-certified solver for either constant
language under any ensemble.

General heuristic schemes currently share the three-answer output type;
giving up counts as failure. Removing give-up outputs without worsening
failure probabilities is a future normalization lemma.

At positive input lengths
`n`, the encoded size `n + k + 1` is at most `3*n*k`, while `n*k` is at most
the square of the encoded size. Thus polynomial bounds match the paper's
`poly(n/δ)` at `δ = 1/k`. Length zero is handled by the encoded size's `+1`.

For a rational request `δ`, `RationalAccuracy.reciprocalIndex` uses
`k = ceil(1/δ)`. Proved lemmas show `1/k ≤ δ` and `k < 1/δ + 1`. These justify
the numerical reparameterization, not a runtime guarantee for reading
arbitrarily verbose rational encodings. We have not yet proved a full
equivalence between machine models with different accuracy encodings.

Also still pending: Levin's moment condition, fixed-budget/time-bounded
classes, oracle reductions and domination, and the Section 2 reduction theorems. The mathematical specification is in
`section2-definitions.md`.

## Amplification results

`Amplification.Basic` defines a plurality vote on three independent executions:
return the common answer when any pair agrees; otherwise return the first.
For any one answer value with probability `u ≤ 1/4`,
`Amplification.Bounds` proves its new probability is at most `(29/32)*u`.
The proof enumerates the finite distribution, then establishes a real
polynomial inequality. It does not assume the answer is a Boolean rather
than giving up.

After `d` levels the bound is `(29/32)^d*u`, using `3^d` base executions.
`Amplification.Runtime` certifies strict PPT for each **fixed** depth, using
independent monadic calls, finite deterministic postprocessing, and the
dependency's machine-level composition theorems.

- `amplification_constant`: for every fixed real `ε > 0` there exists one
  depth, independent of the input and reciprocal accuracy index, that gives
  wrong-answer probability `< ε` on supported inputs and keeps the mass of
  inputs with give-up probability `≥ ε` below `1/k`.
- `AmplifiedErrorlessConditions.toErrorlessConditions`: any threshold
  at most `1/4` implies the original errorless conditions.
- `AmplifiedErrorlessConditions.toHeuristicConditions`: any threshold
  `error` with `error + error ≤ 1/4` gives heuristic conditions, by adding
  the wrong-answer and give-up probabilities outside the exceptional set.
- `AvgBPP.toHeurBPP`: invokes `amplification_constant` with `ε = 1/8`,
  then applies the general conversion lemma. No particular depth is assumed.

The explicit eight-level bound `amplifyPMF_eight_lt_ennreal` remains only as
an optional numerical example in `Amplification.Bounds` (and its tests).
There is no separate eighth-error scheme definition or amplification proof.

### Efficient exponential-error amplification

`Amplification.Flat.Basic` defines flat plurality over all independent runs.
Its deterministic winner appears at least `N/3` times. For an answer of
probability at most `1/4`, this exceeds its mean by at least `N/12`.
`Amplification.Flat.Bounds.flatPMF_rare_le` applies the dependency's finite-PMF
Hoeffding theorem to obtain

\[
\Pr[\text{plurality returns }a] \le \exp(-N/72),\qquad N>0.
\]

`Amplification.Flat.Runtime` certifies repetition and the actual vote-counting
algorithm. Counts are computed by filtering and taking length; unary count
comparisons and branch selection are certified deterministic operations.
This is not a constant-time assumption about an arbitrary list function.

For fixed natural `rate = r`, choose

\[
N=72(r+1)(L+1),\qquad L=|x|+k+1.
\]

This is linear in the complete encoded input length, not exponential.
The machine also computes the repetition count in polynomial time.
`Amplification.ErrorBounds.exponentialError r n` denotes `exp(-r(n+1))`.
The shift handles length zero explicitly.

- `amplification_exponential`: the certified scheme `A.flatAmplifyLinear r`
  has wrong-answer probability strictly below `exp(-r(n+1))` on supported
  inputs. The input mass on which give-up probability is at least that
  threshold remains strictly below `1/k`.
- `amplification_for_thresholds`: every length-dependent target bounded below
  by one of these exponentials is achievable, without needing to compute
  the target function at runtime.
- `avgBPP_iff_exponential`: for each `r ≥ 2`, existence of such an
  exponential-error certified scheme is equivalent to `AvgBPP` membership.
  The reverse direction uses `exp(-r(n+1)) < 1/4` at all lengths.

Thus efficient downward amplification from the paper's `1/4` conditions to
exponentially small internal error is implemented. Recursive three-run voting
remains available for constant thresholds, but is not used for this theorem.

### Caveat about the printed upper interval

Interpreting Lemma 2.1's upper interval as an unrestricted equivalence of
complexity classes is problematic. For threshold `2/5`, the fixed distribution

\[
\Pr[0]=\Pr[1]=3/8,\qquad \Pr[\bot]=1/4
\]

has wrong-answer probability below `2/5` for either true label and give-up
probability below `2/5`. Therefore it meets the two semantic conditions for
**every** language. It can be sampled with three fair bits; the current
`ThresholdCaveat.looseThreshold_conditions` formally checks the probability
conditions but does not add a machine certificate for that sampler.
We do not assert an unrestricted threshold-equivalence claim. This caveat
does not contradict one-way amplification from an existing quarter-error
scheme. A formal complexity-class separation is not claimed by the code.

## Validation

```sh
lake build
lake env lean Tests/Accuracy.lean
lake env lean Tests/Classes.lean
lake env lean Tests/Amplification.lean
lake env lean Tests/ExponentialAmplification.lean
```

The tests include constant languages, machine-certified deterministic to
randomized inclusions, preservation of the `PSamp` restriction, and rejection
of an always-give-up scheme. They also distinguish wrong-answer probability
from total failure probability.
