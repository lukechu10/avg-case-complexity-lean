# Closure under distributional Turing reductions

## Implemented statements

`AverageCaseComplexity/Reductions/Closure.lean` proves:

- `HeuristicallyReducible.toHeurP`: if the source is heuristically reducible
  to the target and the target belongs to `HeurP`, then the source belongs
  to `HeurP`. This is Lemma 2.2(2), with the previously documented runtime
  and length-zero conventions.
- `ErrorlessReductionConditions.toAvgP`: errorless closure **with the explicit
  additional condition** `T.QueriesSupported source target`.
- `ErrorlesslyReducible.toAvgP_of_fullSupport`: that extra condition is automatic
  when the target ensemble supports every word.
- `ErrorlessReductionConditions.toAvgP_of_global_correct`: an alternative repair
  uses a supplied target solver which is correct-or-give-up on **all words**,
  not just on target support.

There is no unconditional `ErrorlesslyReducible.toAvgP` theorem. The existing
reduction and class definitions have not been silently strengthened. No
randomized-class reduction closure theorem is included in this step.

## Simulation and accuracy allocation

The simulator interprets the reduction's genuine typed machine program with
an `Option`-valued oracle. A target solver's `none` aborts execution and produces
`none`; a Boolean reply continues the adaptive computation. A final `none`
from the reduction itself is also preserved.

`Simulation.lean` proves that if the target solver answers every query on the
true-oracle trace correctly, the simulated answer equals the true-oracle
answer. It also proves that if each such answer is correct or give-up, the
simulation either gives up or equals the true-oracle answer. These statements
do not assume a nonadaptive query sequence: they establish agreement up to
the first unsuccessful oracle call.

For outer accuracy index `k`, execute the reduction at `u = 3k`. Put

```
s = encodedInputLength + 1 = n + u + 2
C = c * s^d                         -- domination factor
N = T.coefficient * s^T.degree      -- reduction clock / maximum query length
j = s * (C+1) * (N+1)               -- target solver accuracy index
```

Here `c,d` are one fixed witness to domination, not input-dependent choices.
The target solver's index `j` is polynomial-time computable in unary. At each
source length, every input uses the same target accuracy.

`badQueryEventProb_le` in `QueryBounds.lean` proves

```
Pr[x outside E encounters a bad true-trace query]
  ≤ C * (N+1) * (1/j)
  ≤ 1/u.
```

The finite union ranges over all target words at lengths `0,...,N`. It counts
each queried word as an event, not as its number of occurrences. Domination
then converts each source query-event mass into target word mass, and summing
at each target length uses the target solver's heuristic guarantee.

The final failure event is contained in the union of:

1. the true-oracle reduction's failure, of mass **less than** `1/u`;
2. its domination exceptional set, of mass **at most** `1/u`;
3. a bad query outside that set, of mass **at most** `1/u`.

The result is strictly less than `3/u = 1/k`. The non-strict exceptional-set
bound therefore does not cause a strictness gap.

## Machine-level runtime certificate

`PolyTimeOracleScheme.simulate_efficient` in `SimulationRuntime.lean` proves deterministic
`ComputableTidilyInPolyTime`, not just an `OracleComp` semantic identity and
not a randomized PPT endpoint.

The simulator executes the library's unchanged finite transition table on
encoded finite configurations. It certifies local tape operations, reply
installation, the finite dispatch on the actual observed symbols, and the
captured target-solver call. An absorbing optional state records abort.

The library's `FiniteConfig.SpaceBound` tracks storage growth at every step;
its encoding bound and the polynomial clock justify bounded iteration via
`ComputableTidilyInPolyTime.iterateWith_spec`. The resulting finite interpreter
is proved equal to the native typed oracle program under `Option`
interpretation. Decoding and accuracy rescaling have separate deterministic
machine certificates. `PolyTimeOracleScheme.compose` packages this into the
actual `PolyTimeDeterministicScheme` used by the closure theorems.

## Why errorless closure needs an extra hypothesis

With the literal support-restricted definitions, the paper's proposed
substitution argument has a pointwise-correctness gap:

- An `AvgP` target solver is only guaranteed correct on target support.
- Domination prevents unsupported queries only **outside** `E`.
- On supported source inputs inside `E`, the target solver may return a wrong
  Boolean answer to an unsupported query rather than giving up.
- The source `AvgP` correctness requirement applies to every supported source
  input, including those in `E`. A small error mass is not enough.

The existential exceptional set is not supplied as an efficiently decidable
set, so the simulator cannot simply reject its members.

A concrete illustration of the proposed simulation's problem is:

- Source and target languages are both constantly false.
- The source ensemble is uniform. The target ensemble at each length is
  concentrated on the all-false word.
- The target solver answers true on `[true]` and false everywhere else.
  It is polynomial time, never gives up, and is correct on all target support.
- The reduction queries `[true]` only on source input `[true,true]` at internal
  index `u=3`; otherwise it returns false. With the true target oracle it is
  always correct. At length two and index three, exclude `[true,true]`, whose
  source mass is `1/4 ≤ 1/3`; all query masses outside the exceptional set are
  zero, so domination holds with coefficient zero.
- Substituting that target solver nevertheless returns true on `[true,true]`
  at outer index `k=1`, violating pointwise source correctness.

This is a counterexample to that particular solver-substitution argument,
**not a complexity-class separation or a proof that no other closure argument
exists**. Both constant-language problems in this example are trivially in
`AvgP`. The full example is mathematical explanation, not a formally certified
reduction witness. `Tests/ReductionClosure.lean` checks the zero-mass target
query and the mismatch between true and substituted replies.

The implemented `QueriesSupported` repair requires every true-oracle query on
every supported source input, at every accuracy, to lie in target support.
Alternatively, a globally correct-or-give-up target solver handles unsupported
queries safely. The planned later two-query construction can be used with the
first theorem once its support property is established; that property is not
assumed merely because it makes two calls.

## Validation

```sh
lake build
lake env lean Tests/Accuracy.lean
lake env lean Tests/Classes.lean
lake env lean Tests/Amplification.lean
lake env lean Tests/ExponentialAmplification.lean
lake env lean Tests/Reductions.lean
lake env lean Tests/ReductionClosure.lean
```
