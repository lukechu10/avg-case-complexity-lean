# Section 2: definitions for formalization

Source: Dmitry Itsykson, *Structural complexity of AvgBPP*,
Annals of Pure and Applied Logic 162 (2010), Section 2, printed pp. 214–217
(PDF pp. 2–5). The central formulas in §§2.3–2.5 were checked against
rendered images of printed pp. 215–216.

This is a mathematical specification, not a coverage inventory. Implementation
status is recorded in `lean-foundations.md`, `section2-closure.md`, and
`section2-corollaries.md`. Explicit conventions and modeling decisions follow.

## 1. Basic notation (§2.1)

- Alphabet: `Σ = {0,1}`.
- Binary words: `Σ*`; length of `x`: `|x|`.
- Words of length `n`: `Σⁿ`.
- Language: a subset `L ⊆ Σ*`, identified with its Boolean characteristic
  function `L(x)`.
- Unary encoding: `1ⁿ`, used as the input to a sampler.
- Giving up: a distinguished output `⊥`, different from both Boolean answers.
  Thus a scheme can have output type `{0,1,⊥}`.
- For nonnegative functions `f,g` on a common domain,
  `f(x) = poly(g(x))` means there is a single polynomial `p` such that
  `∀ x, f(x) ≤ p(g(x))`.

The polynomial is uniform: it does not depend on the particular input or
accuracy parameter.

### Worst-case classes recalled in the paper

- `P`: languages decided by a deterministic polynomial-time Turing machine.
- `BPP`: languages with a polynomial-time randomized Turing machine `M` such
  that `∀ x, Pr[M(x) = L(x)] ≥ 3/4`.
- `EXP`, `BPEXP`: the corresponding definitions with running time bounded by
  `2^{p(n)}` for some polynomial `p`.

These definitions concern all inputs, unlike the support-restricted
correctness requirements below.

## 2. Distributions (§2.2)

### Distribution ensemble

An ensemble `D = (Dₙ)ₙ≥1` assigns a probability mass function to each length:

\[
D_n : \Sigma^n \to [0,1],\qquad
\sum_{x\in\Sigma^n} D_n(x)=1.
\]

- Length-specific support:
  `supp(Dₙ) = {x ∈ Σⁿ | Dₙ(x) > 0}`.
- Ensemble support: `supp(D) = ⋃ₙ supp(Dₙ)`.
- Event mass: `Dₙ(E) = ∑_{x ∈ E} Dₙ(x)` for `E ⊆ Σⁿ`.
- When the paper writes `D(y)` for a word of arbitrary length, read it as
  `D_{|y|}(y)`, not as a probability distribution on all finite strings.

### Distributional problem

A pair `(L,D)` consisting of a language and a distribution ensemble.
For a class `𝒞` of distributional problems and a class `𝒟` of ensembles,

\[
(\mathcal C,\mathcal D)
=\{(L,D)\mid (L,D)\in\mathcal C,\ D\in\mathcal D\}.
\]

### Polynomial-time samplability: `PSamp`

`D ∈ PSamp` if there is a polynomial-time randomized sampler `S` whose
output on `1ⁿ` has **exactly** distribution `Dₙ`.
In particular the sampler outputs a word of length `n`.

### Uniform ensemble

`Uₙ(x) = 2^{-n}` for every `x ∈ Σⁿ`; `U = (Uₙ)ₙ≥1`.

## 3. Average polynomial time (§2.3)

Write `n = |x|`. A scheme takes an accuracy parameter `δ`; the paper leaves
its representation implicit. The displayed conditions below are for every
admissible `δ` and every length `n`, not just asymptotically in `δ`.

### Levin's polynomial-on-average running time

A function `t : Σ* → ℕ` is polynomial on average with respect to `D` if

\[
\exists\epsilon>0,\qquad
\mathbb E_{x\sim D_n}[t(x)^\epsilon]=O(n).
\]

Equivalently, the displayed expectation is at most `C n` for all sufficiently
large `n`, for some fixed `C`. Merely requiring polynomial expectation of
`t` is **not** the definition used here.

### Deterministic errorless heuristic scheme; `AvgP`

A deterministic algorithm `A(x,δ)` witnesses `(L,D) ∈ AvgP` if:

1. **Effectiveness:** running time is bounded by `poly(n/δ)`.
2. **Correctness:** for every `x ∈ supp(D)`,
   `A(x,δ) ∈ {L(x),⊥}`.
3. **Usefulness:** `Pr_{x∼Dₙ}[A(x,δ)=⊥] < δ`.

The paper states that existence of such a scheme is equivalent to existence
of a solver with Levin-polynomial-on-average running time.

### Randomized solver in Levin's formulation

A randomized algorithm solves `(L,D)` with bounded error if, on every
supported input, `Pr[A(x) ≠ L(x)] < 1/4`.
Its running-time function is the `3/4` stopping-time quantile:

\[
t_A(x)=\min\{t\in\mathbb N\mid
\Pr[A(x)\text{ halts within }t\text{ steps}]\ge 3/4\}.
\]

Existence of this minimum must be established rather than supplied by a
default value when implementing it in Lean.

### Randomized errorless heuristic scheme; `AvgBPP` (Definition 2.1)

A randomized algorithm `A(x,δ)` witnesses `(L,D) ∈ AvgBPP` if:

1. **Effectiveness:** running time is bounded by `poly(n/δ)`.
2. **Correctness:** for every `x ∈ supp(D)`,
   \[
   \Pr_r[A(x,\delta;r)\notin\{L(x),\bot\}]<1/4.
   \]
3. **Usefulness:**
   \[
   \Pr_{x\sim D_n}\left[
     \Pr_r[A(x,\delta;r)=\bot]\ge 1/4
   \right]<\delta.
   \]

Here `r` denotes the machine's internal randomness. The outer probability
is over inputs; the inner probability is over random coins on a fixed input.
"Errorless" does **not** mean zero probability of an incorrect Boolean
answer in this randomized definition.

### Time-bounded versions

- `AvgTime[g]`: same deterministic correctness/usefulness conditions,
  with effectiveness replaced by `O(g(n/δ))`.
- `AvgBPTime[g]`: same randomized correctness/usefulness conditions,
  with effectiveness replaced by `O(g(n/δ))`.
- `AvgEXP = ⋃_{c>0} AvgTime[n ↦ 2^{n^c}]`.

Footnote 2 also introduces `Avg_Lev Time[n^c]`, using a deterministic solver
with runtime `t` satisfying `E_{Dₙ}[t(x)^{1/c}] = O(n)`.
This is auxiliary notation, distinct from the scheme-based `AvgTime`.

## 4. Heuristic classes (§2.4)

### Deterministic heuristic scheme; `HeurP`

There is a deterministic polynomial-time scheme `A(x,δ)` such that

\[
\Pr_{x\sim D_n}[A(x,\delta)\ne L(x)]<\delta.
\]

The running time is bounded by `poly(n/δ)`. Unlike an errorless scheme,
it may give incorrect Boolean answers on an exceptional set of inputs.
There is no pointwise correctness condition.

### Randomized heuristic scheme; `HeurBPP`

There is a randomized scheme with runtime `poly(n/δ)` such that

\[
\Pr_{x\sim D_n}\left[
  \Pr_r[A(x,\delta;r)\ne L(x)]\ge 1/4
\right]<\delta.
\]

Notice the event is now **any failure to equal `L(x)`**, not just giving up.

### Fixed error-budget algorithms

These take only `x`, not an adjustable `δ`. Let `η(n)` be a prescribed
error budget (the paper calls this function `δ(n)`).

- A deterministic `η`-heuristic algorithm satisfies
  `∀ n, Pr_{x∼Dₙ}[A(x) ≠ L(x)] < η(n)`.
- It is errorless if additionally `A(x) ∈ {L(x),⊥}`.
  Here the paper says **for all `x`**, not merely supported `x`.
- `Heur_{η(n)} P`: problems admitting a polynomial-time `η`-heuristic algorithm.
- `Avg_{η(n)} P`: problems admitting a polynomial-time errorless
  `η`-heuristic algorithm.

The paper defines `Heur_{η(n)} BPP` and `Avg_{η(n)} BPP` "similarly".
The natural scheme-based interpretation is to remove the parameter from
`HeurBPP`/`AvgBPP` and replace their outer bound by `η(n)`. This is an
interpretation to record explicitly, not an additional fully displayed
randomized definition in the source.

It likewise introduces the analogous classes with time bound `O(g(n))`
for fixed-budget algorithms:
`Heur_η Time[g]`, `Avg_η Time[g]`,
`Heur_η BPTime[g]`, `Avg_η BPTime[g]`.
For adjustable-parameter heuristic schemes,
`HeurTime[g]` and `HeurBPTime[g]` use `O(g(n/δ))`.

## 5. Deterministic Turing reductions (§2.5, Definition 2.2)

Let `(L,D)` be the source and `(L',D')` the target.
The witness is a deterministic oracle algorithm `T^{L'}(x,δ)`;
its oracle returns the exact characteristic function of `L'`.

Define the query indicator

\[
\operatorname{Ask}_{T,\delta}(x,y)=
\begin{cases}
1 & \text{if }T^{L'}(x,\delta)\text{ queries }y,\\
0 & \text{otherwise.}
\end{cases}
\]

This records whether a query occurs, **not** how often it occurs.

### Errorless reduction

There is such a `T` satisfying:

1. **Effectiveness:** runtime bounded by `poly(|x|/δ)`.
2. **Correctness:** `T^{L'}(x,δ) ∈ {L(x),⊥}` for all `x ∈ supp(D)`.
3. **Usefulness:** `Pr_{x∼Dₙ}[T^{L'}(x,δ)=⊥] < δ`.
4. **Domination:** there is one polynomial `p` such that for every `n,δ`
   there is a set `E_{n,δ} ⊆ Σⁿ` with `Dₙ(E_{n,δ}) ≤ δ` and, for every
   target word `y`,
   \[
   \sum_{x\in\Sigma^n\setminus E_{n,\delta}}
   \operatorname{Ask}_{T,\delta}(x,y)D_n(x)
   \le p(n/\delta)D'_{|y|}(y).
   \]

The paper abbreviates the exceptional set as `Eₙ`; it may depend on `δ`.
The same exceptional set must work for **all** `y` at a fixed `n,δ`.
The exceptional-set bound is non-strict (`≤ δ`), whereas usefulness is
strict (`< δ`).

In particular, outside the exceptional set, a positive-mass source input
cannot query a target string of zero `D'`-mass. This support property will
matter when invoking the target scheme's correctness guarantee. It does not
ensure support preservation on `E`, although errorless source correctness is
pointwise there too. The resulting gap in the paper's proposed errorless
simulation argument, and the explicitly repaired closure theorems, are documented
in [section2-closure.md](section2-closure.md).

### Heuristic reduction

Keep effectiveness and domination, remove pointwise correctness, and replace
usefulness by

\[
\Pr_{x\sim D_n}[T^{L'}(x,\delta)\ne L(x)]<\delta.
\]

## 6. Results in Section 2, distinct from definitions

These are prospective theorem statements, not assumptions to build into
the class definitions:

- Proposition 2.1: Chernoff–Hoeffding. For `N ≥ 1`, independent identically
  distributed random variables `Xᵢ ∈ [0,1]` with mean `μ`, and `ε > 0`,
  \[
  \Pr\left[\left|\frac1N\sum_{i=1}^N X_i-\mu\right|\ge\epsilon\right]
  \le 2e^{-2\epsilon^2N}.
  \]
- Lemma 2.1: amplification of the `1/4` thresholds in Definition 2.1,
  down to exponentially small error. **Caveat:** interpreting the statement
  that both thresholds can be replaced by any common constant below `1/2`
  as an equivalence of the resulting classes is false for the displayed conditions. At threshold `2/5`, an input-independent
  law with `P(0)=P(1)=3/8`, `P(⊥)=1/4` satisfies both conditions for every
  language. This semantic counterexample is checked in
  `Amplification/ThresholdCaveat.lean`. The valid direction being formalized
  is amplification from `1/4` down to exponentially small thresholds.
  This counterexample does not contradict the one-way reading that an
  existing `AvgBPP` scheme can achieve any such target.
- `AvgP ⊆ HeurP` and `AvgBPP ⊆ HeurBPP`.
- Lemma 2.2: the paper states that errorless reductions preserve `AvgP` and
  heuristic reductions preserve `HeurP`. Heuristic closure is implemented.
  Errorless closure is implemented with explicit support-preserving queries or
  a supplied globally correct target solver; the unrestricted stated argument
  does not establish pointwise correctness on the domination exceptional set.
- Corollary 2.1: sufficiently long queries allow transferring fixed-budget
  `Avg_{1/n^c} P` / `Heur_{1/n^c} P` membership to adjustable-parameter
  `AvgP` / `HeurP` membership. Implemented for arbitrary length-dependent budgets,
  including real-exponent inverse powers, using a finite cover of query lengths.
  Fixed-budget errorlessness is global as stated in §2.4, so this does not depend
  on the deferred unrestricted errorless closure statement.
- Corollary 2.2: a quantitative runtime transfer for errorless reductions,
  using a bound on query lengths outside the exceptional set. The cutoff and
  semantic transfer are implemented; the exact printed runtime formula requires
  care because the target accuracy is `ε`, not the outer `δ`. See the corollary
  notes for the completed machine-certified target-cost envelope theorem and
  the paper-shaped specialization with an explicitly enlarged polynomial argument.

## 7. Modeling decisions before writing Lean definitions

1. **Accuracy encoding (chosen):** executable schemes take a positive
   integer `k` in unary, requesting error less than `1/k`. Input `(x,k)` is
   encoded as `1^k 0 x`, of length `|x| + k + 1`. The Lean development proves
   injectivity and polynomial size comparisons with `n*k` for `n > 0`.
   The separate `RationalAccuracy` type retains `0 < δ ≤ 1`; rounding with
   `k = ceil(1/δ)` gives `1/k ≤ δ` and `k < 1/δ + 1`. This is a numerical
   comparison, not a runtime claim for arbitrary rational encodings.
   The paper itself does not specify an encoding or its cost.
2. **Length zero:** the ensemble is initially indexed from `1`, while later
   notation uses natural numbers and arbitrary query strings. We should
   either extend ensembles to `n = 0` explicitly or rule out empty queries.
   Using `max(1,n)` in runtime bounds also avoids a zero size parameter.
3. **Runtime is computational:** an arbitrary function into output
   distributions plus an independently asserted numeric cost is not enough
   to define a complexity class. Use an executable machine/program model
   and a justified cost semantics, preferably reusing Complexitylib/CSLib.
4. **Randomness and runtime:** polynomial-time randomized schemes and
   samplers should have a bound uniform over coin outcomes, not merely an
   expected-time bound. Keep the Levin quantile runtime separate.
5. **Distribution representation:** length-indexed finite PMFs give exact
   sums and make the distinction between input randomness and machine
   randomness explicit. Exact samplability is a property, not a field that
   every ensemble is assumed to satisfy.
6. **Oracle semantics:** retain the actual query trace and charge for the
   ordinary computation and writing queries. Record whether the time bound
   is required only with the target oracle (as displayed in the paper) or
   uniformly over all oracles; this matters for simulation proofs.
7. **Bounds:** polynomial and big-O witnesses must be uniform in both `x`
   and `δ`. General `g(n/δ)` needs an agreed domain and rounding convention
   when `g` is represented as a function on natural numbers.
8. **Support and quantifiers:** do not replace support-restricted
   correctness by global correctness silently. Do not flatten nested
   probabilities into a joint average-error bound: these are different
   properties.
