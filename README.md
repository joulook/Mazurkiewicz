# Mazurkiewicz

A Lean 4 proof of the TruSt stateless model checking algorithm
(Kokologiannakis, Marmanis, Gladstein, Vafeiadis, *Truly Stateless, Optimal
Dynamic Partial Order Reduction*, POPL 2022), ported from the authors' Coq
development and checked against the paper's appendix.

## What is proved

For programs with read and write actions, and any maximally extensible memory
model (sequential consistency is the instance):

| Result | Theorem | File |
|---|---|---|
| Soundness | `Reach.sound_full` | `Trust/Alg.lean` |
| Termination (A.27) | `terminates` | `Trust/Terminate.lean` |
| Completeness (A.30) | `complete` | `Trust/Complete.lean` |
| Optimality (A.32) | `path_unique` | `Trust/Optimal.lean` |
| Explorer specification | `explore_spec` | `Trust/Explore.lean` |
| Runnable explorer | `exploreC_spec` | `Trust/ExploreC.lean` |

`exploreC_spec`: for a bounded program, `exploreC` lists, without repetition,
exactly the well-formed, SC-consistent, full executions.

There is no `sorry`. The only axioms are `propext`, `Classical.choice` and
`Quot.sound` (`Mazurkiewicz/Audit.lean` prints them).

## Build

```bash
lake exe cache get   # Mathlib cache
lake build
```

The build also runs the tests: the number of executions of the paper's example
programs, and agreement of the explorer with an independent interleaving
semantics (`Trust/Oracle.lean`).

## Layout

- `Mazurkiewicz/Lib/`: relations, lists, paths.
- `Mazurkiewicz/Trust/`: events, graphs, programs, Algorithm 1, the theorems.
- `Mazurkiewicz/Models/`: memory models.
