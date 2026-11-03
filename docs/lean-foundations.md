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
The four complexity classes `AvgP`, `AvgBPP`, `HeurP`, and `HeurBPP` are
therefore not defined yet.

The accuracy encoding is now fixed. Next, attach executable programs and
machine certificates using `schemeInputEncoding`. At positive input lengths
`n`, the encoded size `n + k + 1` is at most `3*n*k`, while `n*k` is at most
the square of the encoded size. Thus polynomial bounds match the paper's
`poly(n/δ)` at `δ = 1/k`. Length zero is handled by the encoded size's `+1`.

For a rational request `δ`, `RationalAccuracy.reciprocalIndex` uses
`k = ceil(1/δ)`. Proved lemmas show `1/k ≤ δ` and `k < 1/δ + 1`. These justify
the numerical reparameterization, not a runtime guarantee for reading
arbitrarily verbose rational encodings. We have not yet proved a full
equivalence between machine models with different accuracy encodings.

Also still pending: Levin's moment condition, fixed-budget/time-bounded
classes, oracle reductions and domination, amplification, and the Section 2
reduction theorems. The mathematical specification is in
`section2-definitions.md`.
