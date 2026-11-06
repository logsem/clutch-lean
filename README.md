# clutch-lean

A Lean 4 formalization of a probabilistic programming language with continuous and discrete
sampling, and Total Eris, an Iris-based program logic for proving total correctness and
distribution specifications of probabilistic programs with error credits.

## Contents

- `Metrology/ProbLang`: syntax, notation, small-step and measure-theoretic semantics, execution,
  erasure of presampling tapes, an executable interpreter and sampler. Reals support exact
  arithmetic, `floor` and the elementary functions (`log`, `sqrt`, `exp`, `sin`, `cos`, `atan`,
  `π`), for samplers such as inverse transforms and Box–Muller.
- `Metrology/Iris`: program-state ghost state and error credits.
- `Metrology/TotalEris`: the total weakest precondition, its adequacy, error and presampling
  rules, distribution adequacy, and the reduction of distribution specifications.
- `Metrology/TotalEris/Examples`: verified samplers (Bernoulli, geometric, negative exponential,
  Gaussian, ...) and smaller examples.

## Building

```
lake exe cache get
lake build
lake test
```

`SampleDemo.lean` shows the `#sample` widget, which draws and plots samples from a program.
