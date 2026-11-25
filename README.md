# average_case_complexity

Uses Lean 4.35.0, Mathlib, and
[Complexitylib](https://github.com/cslib-community/complexitylib).
Complexitylib is pinned to `9a34274a0fa6c857c9d6ae2f3dea148048c8b876`
to match Lean 4.35.0. At that revision its Lake package name is
`complexitylib2`, but Lean imports begin with `Complexity.`.

Import specific `Complexity.*` modules as needed; `import Complexity` imports
the entire library and can require a substantial first build.

```sh
lake update complexitylib2
lake exe cache get
lake build
```

## Formalization

The current development starts with Section 2 of Itsykson's *Structural
complexity of AvgBPP*. See:

- [Mathematical definitions](docs/section2-definitions.md)
- [Lean modules, computational model, and current scope](docs/lean-foundations.md)

`AverageCaseComplexity.Classes` defines machine-certified `AvgP`, `AvgBPP`,
`HeurP`, and `HeurBPP`, using unary reciprocal accuracy parameters.
Constant-threshold and efficient exponential-error amplification, as well as
`AvgBPP ⊆ HeurBPP`, are implemented. The documented downward-amplification
result records a caveat about interpreting the paper's upper-threshold
interval as an unrestricted class equivalence. Deterministic oracle execution and the distributional Turing-reduction
definitions are implemented. Heuristic reductions preserve `HeurP`; errorless
closure is proved with an explicit support-preservation hypothesis or a globally
correct target solver. See [the closure notes](docs/section2-closure.md) for the
support issue in the paper's stated errorless argument. Fixed-budget closure
(Corollary 2.1) and the cutoff/runtime infrastructure are described in
[the corollary notes](docs/section2-corollaries.md).

Section 3's [two-query completeness development](docs/two-query-completeness.md)
(`AverageCaseComplexity/Completeness/TwoQuery.lean`) now has a checked binary
codec, bounded universal execution, compact source compilation, sampler mass
bounds, target correctness/usefulness, and a finite-control two-query reduction.
The `complete` theorem is **not yet certified**: the strict polynomial-time
proofs for the sampler and target solver remain.

Additional checks:

```sh
lake env lean Tests/Accuracy.lean
lake env lean Tests/Classes.lean
lake env lean Tests/Amplification.lean
lake env lean Tests/ExponentialAmplification.lean
lake env lean Tests/Reductions.lean
lake env lean Tests/ReductionClosure.lean
lake env lean Tests/Corollaries.lean
```