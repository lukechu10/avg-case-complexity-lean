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
| `Amplification` | Independent three-run plurality, rare-answer contraction, any fixed positive error threshold, runtime preservation, and `AvgBPP.toHeurBPP` |

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
classes, oracle reductions and domination, exponentially-small-error amplification,
and the Section 2
reduction theorems. The mathematical specification is in
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

This is a fixed-threshold version of Lemma 2.1, **not** the full efficient
exponentially-small-error statement. Choosing depth proportional to input
length here uses exponentially many base calls. The full result needs a
flat polynomial-size plurality vote and concentration bounds, or another
more efficient construction.

## Validation

```sh
lake build
lake env lean Tests/Accuracy.lean
lake env lean Tests/Classes.lean
lake env lean Tests/Amplification.lean
```

The tests include constant languages, machine-certified deterministic to
randomized inclusions, preservation of the `PSamp` restriction, and rejection
of an always-give-up scheme. They also distinguish wrong-answer probability
from total failure probability.
