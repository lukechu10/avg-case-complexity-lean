# How the Lean proof of AvgBPP completeness works

Suppose an oracle can answer a Boolean question about a randomized machine, but the machine we want to simulate has *three* possible answers: yes, no, and “give up.” How can a deterministic reduction recover the third answer? It asks twice about the same computation, changing only the answer the oracle should give when the computation is indecisive. Agreement conveys a bit; disagreement conveys “give up.” That is the idea behind Itsykson’s two-query reduction. Making it an *average-case* reduction takes a second idea: design the oracle’s input distribution so that it assigns enough mass to the queries the reduction actually makes.

The formal proof brings these two ideas together in [`Completeness/TwoQuery.lean`](../AverageCaseComplexity/Completeness/TwoQuery.lean). Its last lines are a useful starting point:

```lean
theorem complete :
    WithPSamp AvgBPP problem ∧
      ∀ P : DistributionalProblem, WithPSamp AvgBPP P → ErrorlesslyReducible P problem := by
  exact ⟨⟨problem_avgBPP, distribution_psamp⟩,
    fun P hP => errorlesslyReducible P hP.1 hP.2⟩
```

The left half is **membership**: the target has an AvgBPP solver, and its ensemble is exactly samplable in strict polynomial time. The right half is **hardness**: given those two witnesses for any source `P`, construct an errorless reduction to the *same* target. `ErrorlesslyReducible` does not itself say “two queries.” That stronger fact is proved about the particular witnessing machine, in `CompiledSource.reduction_trace`.

## 1. The two probabilities in the statement

A distributional problem is a Boolean language together with an ensemble `D`. For each `n`, `D n` is a probability mass function on `FixedWord n`, the type `Fin n → Bool`. There is no probability distribution on lengths. When the proof writes `D.wordMass y`, it means the mass of `y` in the component at **its own length**. A source word and its much longer oracle query can therefore have comparable masses without belonging to the same probability space.

The accuracy argument is a positive integer `k` requesting error less than `1/k`. It is presented in **unary** to a heuristic scheme, so polynomial time in `k` is legitimate. For a randomized scheme, fix `x` and `k` and call its law on `Option Bool` **p**. There are two different AvgBPP requirements in [`Schemes.lean`](../AverageCaseComplexity/Schemes.lean):

- On every supported `x`, the *internal* probability of the wrong Boolean answer must be strictly less than `1/4`. `none` is not a wrong Boolean answer.
- At each length `n`, the *outer* mass under `D n` of inputs for which `p none ≥ 1/4` must be strictly less than `1/k`.

Thus “errorless” does **not** say that every random run of the source solver that returns a bit is correct. The **deterministic reduction** has a stronger pointwise obligation: with the true target oracle it may give up on a supported input, but it may not return the wrong bit. Keeping these two contracts distinct explains why the reduction extracts a frequent answer rather than sampling the source solver once.

## 2. A language that makes uncertainty visible

A target instance contains six fields: answer-machine code `M`, input `x`, answer clock `m`, fallback bit `b`, sampler code `S`, and sampler clock `s`. A canonical encoding represents the clocks by strings of ones of the corresponding lengths. The decoder rejects noncanonical spellings, and `Instance.Valid` requires `x.length + burnIn < m`, where `burnIn = 10000`. The language returns `false` on malformed words or invalid instances. The burn-in is a conservative constant for the tail estimates, not a complexity parameter that grows with the input.

On a valid instance, let `p = boundedAnswer M m x`. The language ignores `S` and `s`, and gives a deterministic answer:

| Law of the bounded run | Language bit |
| --- | --- |
| `p none ≥ 1/4` | The supplied fallback `b` |
| `p none < 1/4` | Whichever of `some false` and `some true` is more frequent; ties go to `false` |

In particular, equality at `1/4` is on the **fallback** side. `query_answers_differ_iff` proves that the two fallback versions of a valid instance have different language bits *exactly* on that side. For example, if half the runs give up and every other run returns `true`, the two oracle answers are still `false` and `true`: the rule tests give-up probability **before** it compares the Boolean answers. Conversely, if the two answers agree, their common value is the frequent Boolean answer, not a fallback guess. The sampler fields will matter for the *mass* of this question, not its truth value.

The definition of `instanceBit` uses a PMF, but no implementation is asked to compare real probabilities. A bounded run reads at most `m` fair bits. Give it an entire tape of `m` bits and replay deterministically; tapes that agree on all bits actually used give the same result. [`FairReplay.lean`](../AverageCaseComplexity/Completeness/FairReplay.lean) proves that the probability of an answer is its tape count divided by `2^m`. `exactLanguageBit_eq` therefore implements the truth table by **integer** comparisons, including the boundary and tie cases. This is an exact algorithm, not necessarily a fast one yet.

## 3. Why the target sampler tests reliability

If the target ensemble were just uniform on encoded instances, even the padding used to give a machine enough time could make its queries exponentially unlikely. Instead, the target sampler treats a uniform word as a *seed* describing how to generate an instance. It also filters the results: the solver we will build is allowed to give up on difficult instances, but such instances must have small total mass.

At requested length `N`, Algorithm 3.1 (`sampler`) works as follows:

1. Draw `N` fair bits. If they do not parse as a seed, return the word unchanged.
2. In a parsed seed, take the **length** of the input field and the lengths of the two clock fields. Run the seed’s sampler code for its indicated clock on that requested input length. Truncate or pad its output on the right with `false` to obtain an input `x` of exactly that length.
3. Run the indicated answer machine on `x` independently `200 N²` times. Accept if **one Boolean answer** occupies at least 90% of all trials. Give-ups remain in the denominator.
4. On acceptance, emit the canonical instance with this `x` and the seed’s codes, clock lengths and fallback. Otherwise emit `N` ones.

A seed and a canonical instance are not the same object. In the seed, the old input and the two clock payloads can contain arbitrary bits. On success the input is replaced and the clocks are canonicalized, **without changing the field lengths**. The self-delimiting codec in [`TupleEncoding.lean`](../AverageCaseComplexity/Completeness/TupleEncoding.lean) has length determined by the field lengths. This proves the success case of `sampler_output_length`; the other two branches already return length `N`. Consequently, converting the word-valued sampler into a fixed-length ensemble preserves its law exactly. `distribution_psamp` uses this equality and the machine certificate `sampler_efficient`, not an approximation argument.

### The two mass estimates serve opposite halves of the proof

Write `peak p = max (p (some false)) (p (some true))` and `tail(N) = 2 exp(−N²)`. The 90% test separates two regimes. If the peak is at least 95%, it passes with probability at least `1 − tail(N)` for positive `N`. If the peak is at most 85%, it passes with probability at most `tail(N)`. These are Hoeffding bounds on independent answer indicators: a gap of `1/20` with `200 N²` trials gives exponent `−N²`. For the upper bound either Boolean answer could trigger acceptance. **No classification of the gap between 85% and 95% is needed.**

For a valid instance `z`, put `N = (encode z).length`. Let `q(x)` be the probability that the indicated bounded, normalized sampler produces **this** `z.input`. The mass lemmas say:

- **Lower bound for hardness (`distribution_mass_lower`):** at peak ≥ 95%, the target mass is at least `(1 − tail(N)) · q(x) / seedDenominator z`. Why not just count the seed `encode z`? That would pay `2^(−N)`. Instead, [`SeedMass.lean`](../AverageCaseComplexity/Completeness/SeedMass.lean) counts a whole family of seeds: hold the codes, lengths and fallback fixed, and vary the discarded input and clock bits. Their combined mass pays for the codes and framing, not for every bit of padding. The conservative denominator is `2^20 · (N+1)^10 · 2^(|M|+|S|)`. The polynomial overhead comes from using logarithmic-size length headers rather than unary framing of the payloads.
- **Upper bound for membership (`distribution_mass_upper`):** at peak ≤ 85%, the target mass is at most `tail(N)`. Here counting one family would be insufficient: an upper bound must cover **all** ways to emit `encode z`. A failed parse cannot return that word, because it parses; the failure marker cannot equal any canonical encoding. In the remaining branch, injectivity of encoding forces an accepted output equal to `encode z` to have exactly its machine, clock and input. Conditional on any seed and sampled input that can produce it, the test has the stated small acceptance probability. Averaging preserves the bound.

## 4. Membership: when does the target solver know enough?

For a valid tuple the solver `targetProgram` chooses between two procedures. If `2^m ≤ k`, it returns `exactLanguageBit` and never gives up. Otherwise it draws `200 m²` independent answers and returns a Boolean answer only if it gets an **80%** majority. Notice the change of scale: the sampler’s 90% test uses the **encoded word length** `N`; the solver’s 80% test uses the **simulated clock** `m`.

**Correctness.** Relative to the truth table, the *wrong* bit always has probability at most `3/4` in one simulated run. In the fallback case at least `1/4` of the mass is already on `none`; in the frequent-bit case the less frequent bit has mass at most `1/2`. Raising a bit of mass at most 75% to an observed 80% majority is unlikely: [`MajorityBounds.lean`](../AverageCaseComplexity/Completeness/MajorityBounds.lean) bounds it by `exp(−m²)`, strictly below `1/4` for the clocks in question. Malformed and invalid words are answered correctly without sampling. This proves `targetProgram_correct` independently of the ensemble.

**Usefulness.** At peak ≥ 85% the same gap works the other way: the 80% vote rarely gives up. Thus an input with internal give-up probability ≥ `1/4` must be a low-peak valid instance in the sampling branch (`targetProgram_giveUp_bad`). Each such word has small mass by the **upper** bound of §3. There are at most `2^N` words of length `N`, so their total mass is at most `2^N · tail(N)`. For `N ≥ 3` this is strictly smaller than `1/2^N`. In the sampling branch `k < 2^m ≤ 2^N`, since the clock fits inside the tuple. Hence the mass is below `1/k`. At lengths too small for validity there is no bad word; if `k ≥ 2^N`, every valid word at that length already qualifies for the exact branch. This last case explains why the exponential algorithm is part of the solver: no fixed length-dependent tail alone would work for arbitrarily large `k`.

Lean first proves the argument for **any** ensemble with the low-peak point-mass bound (`avgBPP_of_small_bad_mass`), then instantiates it with `distribution_mass_upper` to obtain `problem_avgBPP`. Together with `distribution_psamp`, this is the left half of `complete`.

## 5. Turning a source witness into two queries

Now fix a source problem `P` in `WithPSamp AvgBPP`. Its witnesses are an algorithm `A` and an exact sampler for its ensemble. The construction needs more slack than the defining constants provide. `amplified_witness` invokes [constant-error amplification](../AverageCaseComplexity/Amplification.lean): a fixed number of levels of independent three-run plurality suffices to make the wrong-answer probability less than 1% on supported inputs, and the outer mass of inputs with give-up probability **at least 1%** less than `1/k`. The latter is not a pointwise guarantee. The small set on which amplification still permits frequent give-ups will be the exceptional set for domination.

A target instance needs *code*, not the abstract witness `A`. There are two pitfalls here. First, a runtime certificate specifying the output law **at a cutoff** need not imply the same law after additional steps. [`SourceClock.lean`](../AverageCaseComplexity/Completeness/SourceClock.lean) supplies a machine that has genuinely halted by a polynomial bound; its output is then stable when the query clock is padded. Second, the reduction may spend polynomial time in `k` writing a query, but the target sampler must also be able to *guess its machine code*. Writing a unary `k` inside that code would cost exponentially in `k` in seed probability. The specialization instead has exactly this form:

```lean
def specializeCode (header : Word) (k : Accuracy) : Word :=
  selfDelimitingCode header ++ k.val.bits
```

The header is fixed for the source machine. The raw binary suffix gives `2^|code k| ≤ C · (k+1)`, and the constructor is itself polynomial time on the original unary accuracy input. The simulated algorithm still receives the usual input `1^k 0 x`; it is **the representation inside the code**, not the source’s accuracy convention, that changed.

[`FairTables.lean`](../AverageCaseComplexity/Completeness/FairTables.lean) proves that choosing between the two transition tables according to each coin reproduces the source run on **that same tape**, not merely a run with similar statistics. [`TableCompiler.lean`](../AverageCaseComplexity/Completeness/TableCompiler.lean) serializes the tables and proves they decode. Averaging the pathwise identity over a fair tape gives `compile_algorithm`; the sampler counterpart `compile_sampler` recovers `P.distribution n` exactly, since normalization is the identity on genuine length-`n` outputs. `compile_source` packages the codes, clocks, size bounds and equalities of laws in `CompiledSource P`. From this point the reduction can use those equalities without unfolding a universal machine.

For `n = |x|`, the two `queryInstance`s contain `code k`, `x`, the fixed sampler code, and polynomial clocks. The answer clock has the form `c·(n+k+2)^d + n + burnIn + 1`; the sampler clock has the form `c'·(n+1)^d'`. The extra `+1` after the burn-in makes the strict validity test hold even at `n = 0`. Only the fallback bit changes. Both queries have the same length, and the original `x` is recoverable from either of them.

`query_efficient` certifies the functions that write those query words. [`Reductions/TwoQueryMachine.lean`](../AverageCaseComplexity/Reductions/TwoQueryMachine.lean) turns two such constructors into a finite-control oracle machine with a uniform polynomial clock. `CompiledSource.reduction` packages the machine, reindexing its finite control to the state type required by the oracle-scheme interface. For **every** Boolean oracle `L`, `reduction_trace` records the false-fallback query first and the true-fallback query second, along with their respective answers. In particular the second query does not depend on the first answer. `reduction_run` says the result is `combine` of those two bits: their common bit if they agree, `none` otherwise.

Take `L` to be the true target language. By the truth table and exact compilation, the reduction gives up **iff** the amplified source gives up with probability at least `1/4`. On a supported input where it does not give up, the mass left on the correct bit is greater than `1 − 1/4 − 1/100`, whereas the wrong bit has mass less than `1/100`. The frequent bit must be correct. This proves deterministic `reduction_correct`. For `reduction_useful`, the inputs on which the reduction gives up are contained in the source’s 1%-give-up set, already of mass strictly below `1/k`.

## 6. Why these particular queries are dominated

Correct answers and two short queries would suffice for an ordinary oracle reduction. They do **not** suffice for a distributional reduction: a frequent source input must not force the solver to answer a question to which the target assigns negligible mass. [`Domination`](../AverageCaseComplexity/Reductions/Definitions.lean) asks for *one polynomial* working at all lengths and accuracies. For each `n,k` the reduction can discard a set `E` of source mass at most `1/k`; that choice must work for **every** query word `y`. The quantity bounded is the source mass outside `E` that asks for `y` **at least once**, not the expected number of times `y` is asked.

Choose `E` to be exactly the inputs of length `n` where the amplified source has give-up probability at least `1/100`. Outside `E`, on positive-mass inputs, both give-up and wrong-answer mass are below 1%, so the correct answer has mass **greater than 98%**. This is where the earlier 95% lower-bound regime pays off. For either query `y` from such an `x`, its bounded sampler produces `x` with exactly the source point mass `P.distribution n x`. By §3, the target mass of `y` is therefore at least that source mass times `(1 − tail(|y|)) / seedDenominator`. Valid tuples are large enough that the numerator is at least `99/100`; the proof only needs `1/2`.

What looked exponential in the denominator is now affordable. The sampler code has fixed length, `2^|code k|` is at most linear in `k+1`, and `|y|` is polynomial in `n+k+2` because its constructor is polynomial time. Thus `seedDenominator_polynomial` bounds the denominator by `c·(n+k+2)^d` for constants depending on the source witness, **not** on `n`, `k`, or `y`. Rearranged, the lower bound says the source point mass is at most a polynomial times the target point mass. A zero-mass source input satisfies that inequality trivially, without invoking correctness outside support.

Finally `reduction_domination` fixes `y`. If no nonexceptional input asks for it, its query mass is zero. Otherwise decode `y`: either fallback query contains the source input unchanged, and canonical encoding is injective. Hence all the source mass counted for `y` comes from **one** `x`, so the pointwise bound just proved suffices. This is why no exponential sum over source inputs reappears at the last step. `reduction_conditions` pairs domination with correctness and usefulness; `errorlesslyReducible` supplies the machine witness, completing the right half of `complete`.

There is a deliberate limit to this conclusion. `queries_supported_outside_exceptional` gives target support for queries from **supported, nonexceptional** inputs. An exceptional computation that always gives up may never pass the reliability filter. The proof does not claim unconditional query support or bypass the extra hypothesis in the separate [closure argument](section2-closure.md).

## 7. Where Lean proves the time bounds

Throughout, the proof separates a mathematical law (`PMF`, with probabilities in `ENNReal`) from a program (`ProbComp`), and both from a machine realizing the program’s law in strict polynomial time (`IsPPTOn`). A `noncomputable` PMF or a classically chosen machine witness in the proof is not an instruction executed by the solver. Conversely, writing a terminating Lean function is not a polynomial-time certificate. Three particularly useful places to follow the passage from definitions to certified computation are:

- **Parsing and bounded replay.** [`TupleDecodingRuntime.lean`](../AverageCaseComplexity/Completeness/TupleDecodingRuntime.lean) bounds length fields before constructing unary data and checks canonical re-encoding. [`RawMachineRuntime.lean`](../AverageCaseComplexity/Completeness/RawMachineRuntime.lean) proves that parsing the header-specified number of fixed-width rows agrees with parsing the actual rows and checking their count. A malformed count is not a promise. [`CompactInputRuntime.lean`](../AverageCaseComplexity/Completeness/CompactInputRuntime.lean) does not materialize an enormous unary `k` from an untrusted binary suffix: a replay only needs the input prefix reachable within its clock.
- **The whole simulation, not just a transition.** [`UniversalStepRuntime.lean`](../AverageCaseComplexity/Completeness/UniversalStepRuntime.lean) certifies a step even on arbitrary configurations. [`FairTableRuntime.lean`](../AverageCaseComplexity/Completeness/FairTableRuntime.lean) maintains a common size bound as replay switches between tables; the intermediate tape contents, output and configuration encodings stay polynomially bounded throughout the fold over the coins. [`BoundedReplayRuntime.lean`](../AverageCaseComplexity/Completeness/BoundedReplayRuntime.lean) exposes the resulting answer and sampler certificates. These are the inputs to `sampler_efficient_of_replay` and `targetProgram_efficient_of_replay`.
- **The apparently exponential branch.** The solver tests `m < k.val.size` (binary digit length), equivalent to `2^m ≤ k`, without first constructing a unary `2^m`. [`ExactVoteRuntime.lean`](../AverageCaseComplexity/Completeness/ExactVoteRuntime.lean) doubles a list of tapes one bit at a time under that guard and proves that each length-`m` tape occurs exactly once. Both the intermediate list sizes and the work of replaying and counting them are charged to the actual input size. This closes the gap between knowing the exact truth table and being allowed to use it in an AvgBPP solver.

To read the development in Lean, start with `complete` in `TwoQuery.lean`; follow `problem_avgBPP` back through the **upper** mass bound and `errorlesslyReducible` back through the **lower** one. Open the runtime modules when the proof calls for a machine witness rather than a probability inequality. To check the result locally:

```sh
lake build
lake env lean Tests/TwoQueryExecution.lean
lake env lean Tests/BoundedReplay.lean
```

[`TwoQueryExecution.lean`](../Tests/TwoQueryExecution.lean) checks the *transitive* axioms of `complete` against `propext`, `Classical.choice`, and `Quot.sound`; successful elaboration alone would not detect a hidden `sorryAx`. [`BoundedReplay.lean`](../Tests/BoundedReplay.lean) is a small executable companion: it follows a two-state machine through compact decoding, a short clock, a Boolean tie, and sampler padding.
