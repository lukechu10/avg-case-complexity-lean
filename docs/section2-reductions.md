# Deterministic distributional Turing reductions

Scope: tasks 1–3 (oracle APIs, execution/query events, and Definition 2.2).
**Lemma 2.2 closure results are intentionally not part of this implementation.**

## Source specification

Itsykson, *Structural complexity of AvgBPP*, §2.5, Definition 2.2,
printed p. 216. The existing mathematical specification is in
[section2-definitions.md](section2-definitions.md), §5.

With source `(L,D)`, target `(L',D')`, reciprocal accuracy `k`, and `δ=1/k`:

- The oracle answers exactly `L'(y)`; it never gives up.
- Correctness is required only on supported source inputs.
- Errorless usefulness is `Pr[T^(L')(x,k)=⊥] < 1/k`.
- For heuristic reductions, replace correctness/usefulness by
  `Pr[T^(L')(x,k) ≠ L(x)] < 1/k`, including give-up as failure.
- There is one polynomial majorant for all lengths and accuracies.
- For each `n,k`, there is **one** exceptional set `E ⊆ FixedWord n`, with
  `D_n(E) ≤ 1/k`, that satisfies domination for **every** target word `y`.
- The dominated quantity is the source probability of querying `y` at least
  once outside `E`, not the expected number of calls to `y`.
- `D'(y)` means the mass of `y` in `D'_(length y)`, not a global distribution
  on strings of different lengths.

## 1. Existing API audit

The pinned Complexitylib provides:

- `Turing.MultiTapeMachine` in
  `Complexity.Computability.Machines.Turing.MultiTape.Machine`:
  ordinary tape instructions and explicit oracle-channel instructions.
- Its `Choose := Id` specialization: deterministic transitions, without coins.
- `MultiTapeMachine.runConfigFrom` in `Machine.Program`: clocked execution
  as a typed `Cslib.OracleComp`, with explicit choice and query handlers.
- `OracleComp.interpret`: execution against an exact oracle in `Id`, or
  substitution of oracle programs for future simulation.
- Generic transcript instrumentation, and query bounds for the probabilistic
  machine specialization.

There is no ready-made **deterministic oracle polynomial-time** predicate.
`IsOraclePPTOn` concerns probabilistic machines and permits clock exhaustion
without halting; it is not used as a deterministic halting certificate here.
The non-oracle `ComputableTidilyInPolyTime` certificate has no oracle channels.

## 2. Machine and execution model

`Reductions.OracleMachine` specializes the library machine to:

- binary alphabet `Bool`;
- finitely many work tapes;
- finite control `Fin stateCount`;
- one oracle channel `Unit`;
- deterministic transition selection `Id`.

A submitted query is the word actually written to the channel's buffer.
Its answer tape receives the singleton `[L'(query)]`. Subsequent instructions
can inspect that tape, so queries are adaptive.

Each table instruction costs one step, including query submission. Writing
query symbols and reading oracle replies require ordinary steps. The oracle's
own computation is external to this cost, as required for an oracle machine.

Execution records a chronological list of submitted query/Boolean-reply pairs.
Repeated calls appear repeatedly in the trace. `Asks` forgets multiplicity;
`askIndicator` is always zero or one.

`PolyTimeOracleScheme` stores the actual machine and one polynomial clock

```
c * (encodedInputLength + 1)^d.
```

It requires proofs that the machine has **halted** by that clock and that its
output is a valid existing two-bit `answerEncoding`. We do not interpret an
unfinished computation as a certified halt, or assume arbitrary functions
have a chosen cost.

The halting and output-format requirements are uniform over all Boolean
language oracles. This is a deliberate stronger restriction: the paper displays
effectiveness only with the true target oracle. The current relation is a
uniform-clock variant of Definition 2.2, not a proved equivalent presentation
of target-only effectiveness. A conversion from target-only polynomial runtime
to this convention is not proved here. Distributional
correctness, usefulness, and domination are evaluated only with that target
oracle.

The query trace is proof instrumentation, not additional charged machine work.
`interpret_programFrom_withTrace` proves that logging calls during interpretation
of the library's machine program gives exactly the recorded execution trace.
`interpret_program` also identifies the resulting configuration without logging.
Its call-count and request-length bounds follow from the machine instructions.

## 3. Distributional definition

`Distributions.WordMass` defines `Ensemble.wordMass y` and proves it agrees
with the length-indexed PMF mass, and is nonzero exactly on ensemble support.
This includes empty strings and the length-zero ensemble component.

`Reductions.Definitions` defines `queryMass` as

```
Pr[x ~ D_n : x ∉ E and T^(L')(x,k) queries y].
```

`queryMass_eq_sum` identifies it with the paper's indicator-weighted finite
sum. `Domination` requires

```
∃ c d, ∀ k n, ∃ E,
  D_n(E) ≤ 1/k ∧
  ∀ y, queryMass ... E y ≤ c * (n+k+2)^d * D'.wordMass y.
```

The global majorant uses encoded size `n+k+2`, which equals encoded input
length plus one. For positive `n`, this is polynomially equivalent to the
paper's `n/δ = n*k`; our extension also gives meaningful bounds at `n=0`.
At length zero this is a deliberate convention, not equivalence with a literal
`p(0)` bound: the chosen factor can grow with `k`. The paper starts with
positive-length ensembles.
Natural monomials `c*(size)^d` provide a uniform nonnegative polynomial
majorant rather than an arbitrary asserted bound function.

`ErrorlessReductionConditions` and `HeuristicReductionConditions` reuse the
existing scheme probability conditions and add domination.
`ErrorlesslyReducible` and `HeuristicallyReducible` existentially quantify over
certified `PolyTimeOracleScheme` witnesses.

## Verification boundary

These are execution foundations and definitions, not closure theorems.
No solver substitution, AvgP/HeurP downward closure, or Lemma 2.2 proof is
included. Those should begin only after the user verifies this model.

## Validation

```sh
lake build
lake env lean Tests/Reductions.lean
```

Tests construct actual finite transition tables, including an adaptive machine
which makes a second empty-word query exactly when its first answer is true.
The trace retains both calls, the query indicator remains one, and `queryMass`
is one rather than two. A constant-language reduction witness checks the
certificate and probability fields without invoking any closure theorem.
