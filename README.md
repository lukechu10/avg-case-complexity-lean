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
interval as an unrestricted class equivalence. This remains a partial formalization; oracle reductions are not yet
implemented.

Additional checks:

```sh
lake env lean Tests/Accuracy.lean
lake env lean Tests/Classes.lean
lake env lean Tests/Amplification.lean
lake env lean Tests/ExponentialAmplification.lean
```