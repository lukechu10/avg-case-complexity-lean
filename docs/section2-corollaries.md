# Section 2 corollaries

Source: Itsykson, printed p. 217 (PDF p. 5). The displayed formulas were also
checked in the rendered PDF, not only in extracted text.

## Fixed-budget algorithms and Corollary 2.1

`FixedBudget.lean` defines machine-certified deterministic algorithms with no
accuracy input, `HeurFixedP η`, and `AvgFixedP η`. Errorless fixed-budget
algorithms are correct-or-give-up on **all words**, as specified in Section 2.4.
This is stronger than the support-restricted correctness of adjustable schemes.

`Reductions/FixedBudget.lean` proves:

- `HeuristicReductionConditions.toHeurP_of_fixedBudget`;
- `ErrorlessReductionConditions.toAvgP_of_fixedBudget`.

Both results hold for an arbitrary length-dependent error budget `η` and thus
include the inverse-polynomial case, for both natural and real exponents. The errorless result does not assume query
support preservation and does not use the deferred unrestricted AvgP closure:
the fixed target algorithm is already globally correct-or-give-up.

### Distinct query lengths, not maximum length

`T.FixedBudgetBound source target η` supplies:

1. one fixed polynomial domination majorant;
2. a finite cover of all true-oracle query lengths at each source length and
   accuracy, whose cardinality is bounded by `lengthCount n k`;
3. the target error-budget inequality on every queried word.

The cover is uniform over all source words of a given length. Counting calls
on one run is not enough if different source words produce different lengths.
The proof in `QueryLengthBounds.lean` charges the cardinality of this finite
cover, not the maximum query length.

At internal accuracy `u = 3k`, write `C` for the domination factor, `f` for the
length-count bound, and `s = n+u+2`. The proof uses the positive index

```
j = s * (C+1) * (f+1).
```

It requires `η(|y|) ≤ 1/j` on true-oracle queries. The arbitrary-budget theorem
covers real-exponent budgets too. `FixedBudgetBound.of_inversePolynomial`
discharges this using the natural-exponent inequality `j ≤ |y|^c`;
`FixedBudgetBound.of_inversePower` handles arbitrary real exponents with the
same inequality in ENNReal. For positive `c` this is the root-free form of
the paper's lower bound. No rounded root has to be computed to express it.

It is important not to replace `f` by the maximum query length here. That
would make the lower query-length requirement impossible for exponents at most
one, and would make the later padding argument unusable.

The requested `j` is a proof budget: the fixed algorithm never receives it.
Consequently the generic theorem need not assume its finite cover or the
function `η` is executable. `fixedBudgetAccuracy_efficient` separately proves
unary computability of `j` when an efficient count bound is supplied, for use
in later padding constructions.

### Strictness and length zero

The outer probability is bounded by reduction failure `< 1/u`, exceptional
mass `≤ 1/u`, and bad-query mass `≤ 1/u`. Thus the final bound is strictly
`< 1/k`, including when domination or the length count is zero.

`inversePolynomialError c n` is ENNReal `(n^c)⁻¹`. At `n=0` and `c>0` it is
infinite; the query-budget condition then excludes empty queries. No division
by zero is silently treated as a positive finite error budget.

## Explicit time classes

`TimeClasses.lean` adds actual `ComputableTidilyInO` certificates for
input-wise time-bounded schemes and fixed-budget algorithms. It defines
`AvgTimeWithBound`, `HeurTimeWithBound`, `AvgTime`, `HeurTime`, `AvgFixedTime`,
`HeurFixedTime`, and deterministic `AvgEXP`.

The one-variable adjustable classes use `g(n+k+2)`, the project's actual
encoded-size convention. Polynomial equivalence with the paper's positive-length
`nk` parameter does **not** imply equivalence for arbitrary `g`; none is claimed.
`AvgTimeWithBound` leaves the exact input-wise bound explicit when needed.

## Query cutoffs and Corollary 2.2

`Reductions/Cutoff.lean` defines a cutoff handler which checks query length
**before** invoking the target solver. Oversized queries abort with give-up.
`T.CutoffBound` requires both domination and the sharper query-length bound
outside the **same** exceptional set. Independent exceptional sets cannot be
charged as though they were one.

The distributional cutoff-transfer theorems are proved. Errorless transfer
retains either the explicit support-preservation condition or a supplied globally
correct target solver. The cutoff alone does not repair arbitrary unsupported
queries inside the exceptional set.

`cutoffAnswer_inO` certifies the individual cutoff target call, including the
cutoff decision, input reconstruction, and target execution. Its target-cost
bound is the finite envelope

```
H(a) = max over 0 ≤ m ≤ cap(a) of τ(m + j(a) + 2).
```

The maximum requires no monotonicity of `τ`, and is not computed by the source
algorithm. If `τ` is monotone, `queryTimeEnvelope_le_of_monotone` bounds it by
`τ(cap(a) + j(a) + 2)`.

### The exact printed runtime formula needs care

The paper displays `poly(n/δ) * τ(π(n,1/δ)/δ)`. But the simulation in the proof
of Lemma 2.2 calls the target at accuracy `ε`, with reciprocal containing the
domination and query-length-count factors, not just `1/δ`. For arbitrary `τ`,
a polynomial inflation of its argument cannot simply be moved into a
polynomial multiplicative factor. Monotonicity alone does not justify that.

A quantitative theorem must therefore keep the actual target accuracy visible,
or explicitly assume a scaling property sufficient to obtain the shorter
printed formula. No unrestricted version of that absorption is assumed here.

### Completed runtime and class-level statements

`SimulationArbitrary.lean` proves `PolyTimeOracleScheme.simulate_arbitrary_inO`.
It starts from the actual handler machine certificate, certifies each finite
instruction and optional abort state, and applies the library's quantitative
bounded-iteration theorem. A source-preserving invariant and a fixed global
`FiniteConfig.SpaceBound` encoding coefficient bound every stored interpreter
state independently of target runtime. Postprocessing and accuracy rescaling
are also machine-certified. The final target envelope occurs **linearly**, not
inside an extra interpreter-dependent power.

The assembled statements in `Corollaries.lean` are:

- `ErrorlessReductionConditions.toAvgTimeWithBound`: with support-preserving
  queries, source time is `O(s^d * (H(x,3k)+1))` for some fixed `d`;
- `ErrorlessReductionConditions.toAvgTimeWithBound_of_global_correct`: the
  alternative repair with a supplied globally correct-or-give-up target solver;
- `HeuristicReductionConditions.toHeurTimeWithBound`: corresponding heuristic
  transfer without the errorless support hypothesis;
- `ErrorlessReductionConditions.toAvgTimeWithBound_monotone`: for monotone
  `τ`, replace the finite envelope by its endpoint;
- `ErrorlessReductionConditions.toAvgTimeWithBound_enlarged`: for monotone `τ`,
  produce an explicitly enlarged polynomial-time-computable argument `π'` and
  a paper-shaped bound `O(s^d * (τ(π'(x,k)*k)+1))`.

Here `s = |x|+k+2`. The enlarged argument includes the internal accuracy:

```
π'(x,k) = cap(x,3k) + j(x,3k) + 2.
```

It majorizes the accepted query lengths; its unary polynomial-time machine
certificate is part of the theorem. If the original cutoff depends only on
source length and accuracy, so does this enlarged argument. It is deliberately
**not** identified with the originally supplied, sharper cutoff. Thus no
unjustified polynomial-argument absorption is needed.

The unrestricted support-errorless statement remains deferred, as agreed.
Likewise the exact printed formula with an unchanged sharp cutoff and arbitrary
nonmonotone `τ` is not claimed.

## Validation

`lake build` and all seven test files pass, including `Tests/Corollaries.lean`.
The tests include real fixed-target machine witnesses, positive-accuracy and
length-zero cases, the exponent-one padding budget, real exponents, the cutoff
before target execution, class-level quantitative transfer, and a quantitative
certificate for the actual adaptive oracle transition table from the reduction
tests. Axiom checks show only `propext`, `Classical.choice`, and `Quot.sound`.
