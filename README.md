# Mazurkiewicz

Machine-checked theory of optimal stateless model checking in Lean 4:

1. the TruSt algorithm (Kokologiannakis, Marmanis, Gladstein, Vafeiadis,
   *Truly Stateless, Optimal Dynamic Partial Order Reduction*, POPL 2022),
   ported from the authors' Coq development and checked against the paper's
   appendix;
2. its extension with symbolic events, ConDpor (*Optimal Concolic Dynamic
   Partial Order Reduction*, CONCUR 2025);
3. read-modify-write accesses with atomicity, and locks (`lock`, `tryLock`,
   `unlock`, repeated acquires by the holder);
4. `k`-induction over execution graphs under sequential consistency.

## TruSt

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

## ConDpor (`Mazurkiewicz/Condpor/`)

Programs with constraint evaluations; a solver decides them. The theorems are
those of TruSt for the algorithm with symbolic events, for every maximally
extensible memory model lifted to symbolic graphs.

| Result | Theorem | File |
|---|---|---|
| Soundness | `Condpor.Reach.sound_full` | `Condpor/Alg.lean` |
| Termination | `Condpor.terminates` | `Condpor/Terminate.lean` |
| Completeness | `Condpor.complete` | `Condpor/Complete.lean` |
| Optimality | `Condpor.path_unique` | `Condpor/Optimal.lean` |
| Explorer specification | `Condpor.explore_spec` | `Condpor/Explore.lean` |
| Runnable explorer | `Condpor.exploreC_spec` | `Condpor/ExploreC.lean` |
| Reads-from equivalence (TruSt, Algorithm 2) | `Condpor.completeR` | `Condpor/Rf/` |

Also: the solver-call savings of the paper's Section 4.1 (`Concolic.lean`),
`GetNext` (`GetNext.lean`), and the counts of the motivating example
(`Stack.lean`, `StackEx.lean`).

## Read-modify-write and locks (`Mazurkiewicz/Condpor/Rmw/`)

An access may be exclusive; the memory model asks that an exclusive write
directly follows, in coherence order, the write its exclusive read reads
(atomicity). TruSt's Coq development has no such accesses; this part
formalises the argument of the paper's appendix.

| Result | Theorem | File |
|---|---|---|
| (P7), (P8) of Proposition A.22: the read of a pair whose write is missing is the maximal event, and its write is the next event | `Rmw.pending` | `Rmw/Inv.lean` |
| Completeness | `Rmw.complete`, `Rmw.complete_sc` | `Rmw/Complete.lean` |
| A blocked configuration has no fruitful continuation (A.33) | `Rmw.blocked_of_fruitless` | `Rmw/Exit.lean` |
| Explorer specification | `Rmw.explore_spec`, `exploreAt_spec` | `Rmw/ExploreC.lean` |
| Locks: the theorems above for every lock program | `lockSys_explore`, `lockSys_complete`, `lockSys_eq_of_abs_eq` | `Rmw/Locks.lean` |
| Locks: mutual exclusion | `lockSys_mutex` | `Rmw/LockMutex.lean` |

With exclusive accesses a reached configuration can be neither full nor have
a step (`wfaa2_dead`, `faar_dead`, `faa3_dead`, `lock_dead` in
`Rmw/Instances.lean`); `Rmw.blocked_of_fruitless` is the statement that holds.

A lock is a location with the values `0` and `1` and a hold count per thread.
`lock` reads exclusively and, on `0`, writes `1` exclusively, otherwise the
thread blocks; `tryLock` is the same but a failed attempt returns and writes
nothing; an acquire by the holder and a release that is not the last are
local; `unlock` by a thread that does not hold the lock is an error event.
`Rmw/LocksEx.lean` and `Rmw/LocksEx3.lean` compute the executions of eighteen
small lock programs (T0 to T17) in the kernel.

## PCT (`Mazurkiewicz/Pct/`)

Randomized testing with a depth bound (Burckhardt, Kothari, Musuvathi,
Nagarakatte, *A Randomized Scheduler with Probabilistic Guarantees of Finding
Bugs*, ASPLOS 2010), for programs given as prefix-closed sets of schedules.
"Violates" is read on prefixes, and the labelling is strict (a thread has
started before its step has a name, and the next name of a thread changes
only when the thread moves); the paper's proof uses both without stating
them.

| Result | Theorem | File |
|---|---|---|
| A step emits the next name of its thread | `Labelling.names_cons` | `Pct/Basic.lean` |
| The directed run never violates the directive | `Inv.step` | `Pct/Directed.lean` |
| Coverage, deterministic form | `coverage` | `Pct/Coverage.lean` |
| Coverage as a count | `card_good`, `card_params` | `Pct/Count.lean` |
| A strongly hitting schedule exists | `exists_stronglyHits` | `Pct/Hitting.lean` |
| Strong `d`-hitting gives `(d+1)`-hitting | `hits_of_stronglyHits_tail` | `Pct/Hitting.lean` |
| Condition 1 from one complete schedule (static programs) | `cond1_of_complete` | `Pct/Static.lean` |
| A p-guaranteeing directive gives a strongly guaranteeing tuple | `stronglyGuar_of_pguar` | `Pct/Static.lean` |
| A guaranteeing tuple gives a p-guaranteeing directive | `pguar_chainDir` | `Pct/Static.lean` |
| A strongly guaranteeing tuple gives a p-guaranteeing directive | `exists_pguar_of_stronglyGuar` | `Pct/Static.lean` |
| The position labelling is a strict labelling | `posLab_strict`, `cntLab_strict` | `Pct/Position.lean` |
| Violation of a position directive, by order | `Labelling.IsPos.pviolates_iff_viol` | `Pct/Position.lean` |
| The schedules of a program are a local schedule set | `Program.sched_local` | `Pct/Program.lean` |
| The schedules of `P⁺`, by the schedules of `P` | `Program.mem_sched_plus_iff` | `Pct/Program.lean` |
| Static bounded programs have thread lengths | `Program.Static.hasLen_plus` | `Pct/Program.lean` |
| The order word of a schedule is a partial schedule of the positions | `psched_ordP`, `Program.Static.psched_ord` | `Pct/Program.lean` |
| Every partial schedule of the positions is an order word | `Program.Static.exists_sched_ord_eq` | `Pct/Program.lean` |
| Linear extensions of the positions and complete schedules | `Program.Static.exists_complete_ord_eq`, `Program.Static.complete_iff` | `Pct/Program.lean` |
| p-guarantee on schedules and on the poset of positions | `Program.Static.pguarantees_iff_pguar` | `Pct/Program.lean` |
| A p-guaranteeing directive gives a strongly guaranteeing tuple, on schedules | `Program.Static.stronglyGuar_of_pguarantees` | `Pct/Program.lean` |
| A guaranteeing tuple gives a p-guaranteeing directive, on schedules | `Program.Static.pguarantees_chainDir` | `Pct/Program.lean` |
| A strongly guaranteeing tuple gives a p-guaranteeing directive, on schedules | `Program.Static.exists_pguarantees_of_stronglyGuar` | `Pct/Program.lean` |
| Complete schedules of `P⁺`, by the complete schedules of `P` | `Program.complete_plus_iff` | `Pct/Program.lean` |
| A free step creates no p-violation | `Directive.PGuarantees.not_pviolates_freeStep` | `Pct/Free.lean` |
| A complete schedule with free steps only is in the bug | `Directive.PGuarantees.mem_of_free_complete` | `Pct/Free.lean` |
| A free step exists; a complete schedule with free steps only exists (bounded programs) | `Directive.exists_freeStep`, `Directive.PGuarantees.exists_free_complete_mem` | `Pct/Free.lean` |
| Depth 1: the schedules that run the thread of the target last are in the bug | `Prog.HasLen.mem_of_thr_last_one` | `Pct/Free.lean` |

`coverage`: for every initial priority order that puts the thread of the
first target last there are `d - 1` distinct change points within the length
bound such that RandS with these parameters reaches a complete schedule and
every complete schedule it reaches is in the bug. `card_good`: for threads
`0, …, n` and length bound `K`, at least `n!` of the `(n+1)! K^(d-1)`
parameters of RandS (a permutation and `d - 1` change points) are such; a
uniformly chosen parameter finds the bug with probability at least
`1/((n+1) K^(d-1))`.

## Induction (`Mazurkiewicz/Induction/`)

`k`-inductive sets and bars over execution graphs, with executable checkers
and worked examples, for plain programs under sequential consistency.

## Axioms

There is no `sorry`. The only axioms are `propext`, `Classical.choice` and
`Quot.sound` (`Mazurkiewicz/Audit.lean` prints them).

## Build

```bash
lake exe cache get   # Mathlib cache
lake build
```

The build also runs the tests: the numbers of executions of the papers' example
programs and of the lock programs, and agreement of the explorer with an independent interleaving
semantics (`Trust/Oracle.lean`).

## Layout

- `Mazurkiewicz/Lib/`: relations, lists, paths.
- `Mazurkiewicz/Trust/`: events, graphs, programs, Algorithm 1, the theorems.
- `Mazurkiewicz/Models/`: memory models.
- `Mazurkiewicz/Condpor/`: symbolic events; `Rf/` the reads-from version;
  `Rmw/` exclusive accesses and locks.
- `Mazurkiewicz/Induction/`: `k`-induction.
- `Mazurkiewicz/Audit.lean`: the axioms of the main theorems.
