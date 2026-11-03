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