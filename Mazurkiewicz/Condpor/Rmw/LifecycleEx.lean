import Mazurkiewicz.Condpor.Rmw.Lifecycle

/-!
# Thread lifecycle: programs and targets

The programs of the targets of `LIFECYCLE-DESIGN.md` §4 (draft 4.2). Threads are `0..k`,
thread `0` is the root unless said otherwise, `st t = 10 + t` (as in the reviewers' hand
encodings), the lock is location `0` (and `1` in `dl2`, `dl2j`), data locations are `1`
and `2`. Each program is evaluated at its adequate bound `2·(longest code) + 3`, except
`cutErr` (bound `2`, inadequate on purpose).

A target `P_target` states, by kernel evaluation (`decide +kernel`) on `exploreCfgAtF`
(whose graphs are those of `exploreAt`, `lifeTarget_head`, hence by `lifeSys_explore`
exactly the well-formed full SC-consistent atomic executions of the compiled program):
the program is in the fragment, the bound is adequate, and `lifeTarget` = [full graphs, cut,
exploration, error, blocked, deadlock, complete, odd, and the signature counts of
error, blocked, deadlock, complete]. `odd` (a `block` outside the kind table of §3) is `0`
everywhere, as `lc_lemma7` predicts.

Expected numbers and their sources (terminal-valid classes; exploration where a Lean dump
exists). d1, d2: Lean hand encodings of `opus-life-d1`, `opus-life-d2` (`out/*.tsv`,
second column; data coherence omitted); d3, d4: `opus-life-d3/out/gate3.log`,
`opus-life-d4/out/gate-count.log` (hand encoding = machine, per class); sig: `proj.py` on
the d1/d2 dumps; hand: derived before the evaluation (see `LC1-impl.md`); mach: the §5
machine of `opus-life-d4/machine.py` run by the implementer.

| program | expected (source) | evaluated |
|---|---|---|
| `startNoJoin` | 1 compl, 1 expl, sig 1 (d1, sig, hand) | equal |
| `startJoin` | 1 compl, 2 expl, sig 1 (d1, sig, hand) | equal |
| `neverStarted` | 1 compl, sig 1 (d1, sig) | equal |
| `joinThenStart` | 1 compl, 2 expl, sig 1 (d1, sig) | equal |
| `raceJoin` | 3 compl, 5 expl (d2 dump, full graphs; d2 projection: 2), sig 1 | equal |
| `errStale` | 1 error, 1 expl (d4 gate, hand) | equal |
| `errTwo` | 1 error, 3 expl (d3) | equal |
| `queryData` | 3 compl, 1 expl (d3 `query`, d4) | equal |
| `asmRead` | 1 blocked, 1 compl, 2 expl (d3) | equal |
| `asmLockRd` | 1 blocked (d3) | equal |
| `lockAcross` | 1 deadlock, 1 expl (d3) | equal |
| `joinErr` | 1 error, 1 expl (d3) | equal |
| `workerStarts` | 2 compl, 6 expl (d3) | equal |
| `pubVis` | 1 compl, 2 expl (d3) | equal |
| `rptJoin` | 1 compl, 2 expl (d3) | equal |
| `nsHeld` | 1 compl (d4) | equal |
| `nsHeld2` | 1 deadlock, 1 expl (d4) | equal |
| `queryRace` | 3 compl (d4) | equal |
| `queryTry` | 6 compl, 2 expl (d4) | equal |
| `errFinal` | 1 error, 7 expl (d4) | equal |
| `asmFinal` | 1 blocked, 3 expl (d4) | equal |
| `joinCycle` | 1 deadlock, 1 compl, 5 expl (hand; mach: 1 deadlock, 1 compl) | equal |
| `joinUnderLock` | 1 deadlock, 1 compl, 3 expl (hand; mach: same terminal) | equal |
| `cutErr` | 1 cut, 1 expl (hand) | equal |
| `twoStarters` | 2 compl, sig 1 (mach; two starters of different threads) | equal; 8 expl |

Rejected programs: one per rule of §2.2; each breaks exactly its rule (`*_rule`).
-/

namespace Condpor

namespace Life

/-- Threads `0..k`, roots `roots`, locks `locks`, `st t = 10 + t`. -/
def mkP (k : ℕ) (roots : List Tid) (locks : List Loc) (code : Tid → List TOp) : LProg :=
  ⟨List.range (k + 1), List.nodup_range, roots, locks, fun t => 10 + t, code⟩

/-- `lock 0; unlock 0`. -/
def cs : List TOp := [.lock 0, .unlock 0]

/-- Main starts the listed threads, runs `body`, then joins `1..k`. -/
def mainOf (k : ℕ) (starts : List Tid) (body : List TOp) : List TOp :=
  starts.map TOp.start ++ body ++ (List.range k).map (fun i => TOp.join (i + 1))

/-! ### Round 1-2 programs (`opus-life-d1`, `opus-life-d2`) -/

def startNoJoin : LProg := mkP 1 [0] [0] fun | 0 => [.start 1] | 1 => [.wr 1 1] | _ => []
def startJoin : LProg := mkP 1 [0] [0] fun | 0 => [.start 1, .join 1] | _ => []
def neverStarted : LProg := mkP 1 [0] [0] fun | 0 => .join 1 :: cs | 1 => cs | _ => []
def joinThenStart : LProg := mkP 1 [0] [0] fun
  | 0 => [.join 1, .start 1, .join 1] | 1 => cs | _ => []
def lowChild : LProg := mkP 2 [0] [0] fun
  | 0 => [.start 2, .lock 0, .unlock 0, .join 2, .join 1] | 1 => cs | 2 => .start 1 :: cs
  | _ => []
def lmin3 : LProg := mkP 2 [0] [0] fun
  | 0 => mainOf 2 [1] cs | 1 => .start 2 :: cs | _ => []
def lmin3e : LProg := mkP 2 [0] [0] fun
  | 0 => mainOf 2 [1] [.rd 0] | 1 => .start 2 :: cs | _ => []
def creator : LProg := mkP 2 [0] [0] fun
  | 0 => mainOf 2 [1, 2] cs | 1 => cs | _ => []
def dl2 : LProg := mkP 2 [0] [0, 1] fun
  | 0 => mainOf 2 [1, 2] []
  | 1 => [.lock 0, .lock 1, .unlock 1, .unlock 0]
  | 2 => [.lock 1, .lock 0, .unlock 0, .unlock 1]
  | _ => []
/-- `dl2` with a third worker that joins a deadlocked thread (`joinDead`). -/
def dl2j : LProg := mkP 3 [0] [0, 1] fun
  | 0 => mainOf 3 [1, 2, 3] []
  | 1 => [.lock 0, .lock 1, .unlock 1, .unlock 0]
  | 2 => [.lock 1, .lock 0, .unlock 0, .unlock 1]
  | 3 => [.join 1]
  | _ => []
def lateJoin : LProg := mkP 2 [0] [0] fun
  | 0 => mainOf 2 [1] [] | 1 => [.start 2, .join 2] ++ cs | 2 => cs | _ => []
def raceJoin : LProg := mkP 2 [0] [0] fun
  | 0 => [.start 1, .start 2] | 1 => [.join 2, .wr 1 1] | 2 => [.wr 1 2] | _ => []
def twoJoin : LProg := mkP 3 [0] [0] fun
  | 0 => [.start 1, .start 2, .start 3] | 1 => [.join 3] | 2 => [.join 3] | _ => []
def errStale : LProg := mkP 1 [0] [0] fun | 0 => [.start 1, .unlock 0] | _ => []

/-! ### Round 3-4 programs (`opus-life-d3`, `opus-life-d4`) -/

def errTwo : LProg := mkP 2 [0] [0] fun
  | 0 => [.start 1, .start 2] | 1 => [.unlock 0] | 2 => [.unlock 0] | _ => []
def reTry : LProg := mkP 1 [0] [0] fun
  | 0 => [.start 1, .lock 0, .lock 0, .unlock 0, .unlock 0, .join 1]
  | 1 => [.tryLock 0 1, .unlock 0] | _ => []
def twoFail : LProg := mkP 2 [0] [0] fun
  | 0 => [.lock 0, .start 1, .start 2, .unlock 0]
  | 1 => [.tryLock 0 1, .unlock 0] | 2 => [.tryLock 0 1, .unlock 0] | _ => []
/-- `query` of round 3, `queryData` of round 4 (the same program). -/
def queryData : LProg := mkP 1 [0] [0] fun
  | 0 => [.start 1, .lock 0, .unlock 0] | 1 => [.rd 0] | _ => []
def asmRead : LProg := mkP 1 [0] [0] fun
  | 0 => [.start 1, .wr 1 1, .join 1] | 1 => [.assume 1 1, .wr 2 1] | _ => []
def asmLockRd : LProg := mkP 0 [0] [0] fun | 0 => [.lock 0, .assume 1 1] | _ => []
def asmStale : LProg := mkP 2 [0] [0] fun
  | 0 => [.start 1, .start 2, .lock 0, .join 1, .unlock 0]
  | 1 => [.assume 1 1] | 2 => cs ++ [.wr 1 1] | _ => []
def lockAcross : LProg := mkP 1 [0] [0] fun
  | 0 => [.lock 0, .start 1, .lock 0, .unlock 0, .join 1, .unlock 0] | 1 => cs | _ => []
def joinErr : LProg := mkP 1 [0] [0] fun | 0 => [.start 1, .join 1] | 1 => [.unlock 0] | _ => []
def workerStarts : LProg := mkP 2 [0] [0] fun
  | 0 => [.start 1, .join 1] | 1 => [.start 2, .wr 1 1, .join 2] | 2 => [.rd 1] | _ => []
def pubVis : LProg := mkP 1 [0] [0] fun
  | 0 => [.wr 1 1, .start 1, .join 1, .rd 2] | 1 => [.rd 1, .wr 2 1] | _ => []
def rptJoin : LProg := mkP 1 [0] [0] fun
  | 0 => [.start 1, .join 1, .join 1] | 1 => [.wr 1 1] | _ => []
def nsHeld : LProg := mkP 1 [0] [0] fun | 0 => [.lock 0] | 1 => [.lock 0] | _ => []
def nsHeld2 : LProg := mkP 2 [0] [0] fun
  | 0 => [.lock 0, .start 2] | 1 => cs | 2 => [.lock 0] | _ => []
def queryRace : LProg := mkP 1 [0, 1] [0] fun | 0 => cs | 1 => [.rd 0] | _ => []
def queryTry : LProg := mkP 1 [0] [0] fun
  | 0 => [.start 1, .lock 0, .rd 0, .unlock 0] | 1 => [.tryLock 0 1, .unlock 0, .rd 0] | _ => []
def errFinal : LProg := mkP 2 [0] [0] fun
  | 0 => [.lock 0, .start 1, .start 2, .unlock 0, .join 2] | 1 => [.unlock 0] | 2 => [.lock 0]
  | _ => []
def asmFinal : LProg := mkP 2 [0] [0] fun
  | 0 => [.start 1, .start 2, .join 2] | 1 => [.assume 1 1] | 2 => [.lock 0, .assume 1 2]
  | _ => []
def twoStarters : LProg := mkP 4 [0] [0] fun
  | 0 => [.start 1, .start 2] | 1 => [.start 3] | 2 => [.start 4] | 3 => [.wr 1 1]
  | 4 => [.wr 1 2] | _ => []

/-! ### New programs (LC1) -/

/-- A join cycle: `T1: join 2 ∥ T2: join 1`, both started by main. -/
def joinCycle : LProg := mkP 2 [0] [0] fun
  | 0 => [.start 1, .start 2] | 1 => [.join 2] | 2 => [.join 1] | _ => []
/-- A join under a lock: main holds the lock while it joins a thread that needs it. -/
def joinUnderLock : LProg := mkP 1 [0] [0] fun
  | 0 => [.start 1, .lock 0, .join 1, .unlock 0] | 1 => cs | _ => []
/-- The cut test: an error in main, a worker cut by the inadequate bound `2`. -/
def cutErr : LProg := mkP 1 [0] [0] fun
  | 0 => [.start 1, .unlock 0] | 1 => [.wr 1 1, .wr 1 2] | _ => []

/-! ### Smaller members of the families tryjoin, chain, diamond, J7 -/

/-- tryjoin without its plain worker `2`. -/
def tryjoin2 : LProg := mkP 2 [0] [0] fun
  | 0 => mainOf 2 [1, 2] []
  | 1 => [.join 2, .tryLock 0 1, .unlock 0]
  | 2 => cs ++ [.tryLock 0 1, .unlock 0]
  | _ => []
/-- A chain of three workers: `1` joins `2`, `2` joins `3`. -/
def chain3 : LProg := mkP 3 [0] [0] fun
  | 0 => mainOf 3 [1, 2, 3] [] | 1 => .join 2 :: cs | 2 => .join 3 :: cs | 3 => cs | _ => []
/-- A chain of two workers: `1` joins `2`. -/
def chain2 : LProg := mkP 2 [0] [0] fun
  | 0 => mainOf 2 [1, 2] [] | 1 => .join 2 :: cs | 2 => cs | _ => []
/-- A diamond of three workers: `1` and `2` join `3`. -/
def diamond3 : LProg := mkP 3 [0] [0] fun
  | 0 => mainOf 3 [1, 2, 3] [] | 1 => .join 3 :: cs | 2 => .join 3 :: cs | 3 => cs | _ => []
/-- J7 without its plain worker `2`: `1` and `2` join the empty thread `3`. -/
def j7s : LProg := mkP 3 [0] [0] fun
  | 0 => mainOf 3 [1, 2, 3] [] | 1 => .join 3 :: cs | 2 => .join 3 :: (cs ++ cs) | _ => []

/-- The diamond family, shrunk: two joiners of the worker `3` instead of three workers
(the plain worker `4` of `diamond` removed), and the critical section of the second joiner
removed: `1: join 3; lock; unlock`, `2: join 3`, `3: lock; unlock`. -/
def diamondB : LProg := mkP 3 [0] [0] fun
  | 0 => mainOf 3 [1, 2, 3] [] | 1 => .join 3 :: cs | 2 => [.join 3] | 3 => cs | _ => []
/-- The J7 family, shrunk: the plain worker `2` of `j7` removed (threads renumbered: the
empty target `4` is `3`), and the critical section of the first joiner removed:
`1: join 3`, `2: join 3; lock; unlock; lock; unlock`, `3` empty. -/
def j7b : LProg := mkP 3 [0] [0] fun
  | 0 => mainOf 3 [1, 2, 3] [] | 1 => [.join 3] | 2 => .join 3 :: (cs ++ cs) | _ => []

/-! ### Outside the fragment: `odd` and a misclassification occur

`lifeClass_ne_odd` needs the fragment. Two programs of Astra's round-1 review (LC1-r1): -/

/-- One root with `st 0 = 10` doing `assume 10 0` (an `assume` of its own lifecycle
location, rule 7): its `block` follows a read of value `1` of `st 0`, which is in no row of
the kind table, so the class is `odd`. -/
def outsideAsmSt : LProg :=
  ⟨[0], by decide, [0], [0], fun t => 10 + t, fun | 0 => [.assume 10 0] | _ => []⟩

/-- One root: `lock 0; assume 0 0` (an `assume` of a lock location, rule 7): the `block`
follows the non-exclusive read of the `assume`, which reads the thread's own acquire `1`;
the classifier takes it for a final lock wait and reports a deadlock. -/
def outsideLockAsm : LProg := mkP 0 [0] [0] fun | 0 => [.lock 0, .assume 0 0] | _ => []

theorem outsideAsmSt_class : fragB outsideAsmSt = false ∧
    lifeTarget outsideAsmSt 5 = [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] := by
  decide +kernel

theorem outsideLockAsm_class : fragB outsideLockAsm = false ∧
    lifeTarget outsideLockAsm 7 = [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0] := by
  decide +kernel

/-- The full programs of the families. Not evaluated in any CI-built file; external runs
(interpreter `#eval` of `lifeTarget`, not theorems) are logged in
`/local/home/mkhoshechin/tmp/rmw-review/lc1-external/<name>.log`. -/
def tryjoin : LProg := mkP 3 [0] [0] fun
  | 0 => mainOf 3 [1, 2, 3] []
  | 1 => [.join 3, .tryLock 0 1, .unlock 0]
  | 2 => cs
  | 3 => cs ++ [.tryLock 0 1, .unlock 0]
  | _ => []
def chain : LProg := mkP 4 [0] [0] fun
  | 0 => mainOf 4 [1, 2, 3, 4] [] | 1 => .join 2 :: cs | 2 => .join 3 :: cs | 3 => cs | 4 => cs
  | _ => []
def diamond : LProg := mkP 4 [0] [0] fun
  | 0 => mainOf 4 [1, 2, 3, 4] [] | 1 => .join 3 :: cs | 2 => .join 3 :: cs | 3 => cs | 4 => cs
  | _ => []
def j7 : LProg := mkP 4 [0] [0] fun
  | 0 => mainOf 4 [1, 2, 3, 4] [] | 1 => .join 4 :: cs | 2 => cs | 3 => .join 4 :: (cs ++ cs)
  | _ => []

/-! ### Rejected programs: one per rule of §2.2

Each program breaks exactly the rule it is named after: `*_rule` states the whole list
`fragChecks` (all twelve rules, `fragB_eq`), with `false` at that rule only. -/

/-- Rule 1: a root that is not a declared thread. -/
def rjRootUndecl : LProg := mkP 0 [0, 5] [0] fun | _ => []
/-- Rule 2: lifecycle locations not injective. -/
def rjStNotInj : LProg :=
  ⟨[0, 1], by decide, [0], [0], fun _ => 10, fun | 0 => [.start 1] | _ => []⟩
/-- Rule 3: a lifecycle location that is a lock location. -/
def rjStLock : LProg := mkP 1 [0] [0, 11] fun | 0 => [.start 1] | _ => []
/-- Rule 4: a lock call on a data location. -/
def rjLockData : LProg := mkP 0 [0] [0] fun | 0 => [.lock 1, .unlock 1] | _ => []
/-- Rule 5: `rd` of a lifecycle location. -/
def rjRdSt : LProg := mkP 1 [0] [0] fun | 0 => [.rd 11] | _ => []
/-- Rule 6: `wr` on a lock location. -/
def rjWrLock : LProg := mkP 0 [0] [0] fun | 0 => [.wr 0 1] | _ => []
/-- Rule 6: `wr` on a lifecycle location. -/
def rjWrSt : LProg := mkP 1 [0] [0] fun | 0 => [.wr 11 1] | _ => []
/-- Rule 7: `assume` on a lock location. -/
def rjAsmLock : LProg := mkP 0 [0] [0] fun | 0 => [.assume 0 0] | _ => []
/-- Rule 7: `assume` on a lifecycle location. -/
def rjAsmSt : LProg := mkP 1 [0] [0] fun | 0 => [.assume 11 1] | _ => []
/-- Rule 8: `start` of an undeclared thread. -/
def rjStartUndecl : LProg := mkP 1 [0] [0] fun | 0 => [.start 5] | _ => []
/-- Rule 9: `start` of a root. -/
def rjStartRoot : LProg := mkP 1 [0, 1] [0] fun | 0 => [.start 1] | _ => []
/-- Rule 9: `join` of a root. -/
def rjJoinRoot : LProg := mkP 1 [0] [0] fun | 0 => [.start 1] | 1 => [.join 0] | _ => []
/-- Rule 10: a thread starts itself (nobody else starts it). -/
def rjSelfStart : LProg := mkP 1 [0] [0] fun | 1 => [.start 1] | _ => []
/-- Rule 10: a thread joins itself. -/
def rjSelfJoin : LProg := mkP 1 [0] [0] fun | 0 => [.start 1] | 1 => [.join 1] | _ => []
/-- Rule 11: two declared threads `1`, `2` each start the declared thread `3` once. -/
def rjTwoStarters : LProg := mkP 3 [0] [0] fun
  | 0 => [.start 1, .start 2] | 1 => [.start 3] | 2 => [.start 3] | _ => []
/-- Rule 11: two starters of `3` that exclude each other only by a `tryLock`. -/
def rjTwoStartersTry : LProg := mkP 3 [0] [0] fun
  | 0 => [.start 1, .start 2] | 1 => [.tryLock 0 1, .start 3]
  | 2 => [.tryLock 0 1, .start 3] | _ => []
/-- Rule 12: two starts on one control path of one thread. -/
def rjTwoStarts : LProg := mkP 1 [0] [0] fun | 0 => [.start 1, .start 1] | _ => []
/-- Rule 12: two starts on the success path of a `tryLock` that skips one on failure. -/
def rjTwoStartsTry : LProg := mkP 1 [0] [0] fun
  | 0 => [.tryLock 0 1, .start 1, .unlock 0, .start 1] | _ => []

/-- The rule list with only rule `i` (1-based) broken. -/
def onlyBroken (i : ℕ) : List Bool := (List.range 12).map (fun j => decide (j + 1 ≠ i))

theorem rjRootUndecl_rule : fragChecks rjRootUndecl = onlyBroken 1 := by decide +kernel
theorem rjStNotInj_rule : fragChecks rjStNotInj = onlyBroken 2 := by decide +kernel
theorem rjStLock_rule : fragChecks rjStLock = onlyBroken 3 := by decide +kernel
theorem rjLockData_rule : fragChecks rjLockData = onlyBroken 4 := by decide +kernel
theorem rjRdSt_rule : fragChecks rjRdSt = onlyBroken 5 := by decide +kernel
theorem rjWrLock_rule : fragChecks rjWrLock = onlyBroken 6 := by decide +kernel
theorem rjWrSt_rule : fragChecks rjWrSt = onlyBroken 6 := by decide +kernel
theorem rjAsmLock_rule : fragChecks rjAsmLock = onlyBroken 7 := by decide +kernel
theorem rjAsmSt_rule : fragChecks rjAsmSt = onlyBroken 7 := by decide +kernel
theorem rjStartUndecl_rule : fragChecks rjStartUndecl = onlyBroken 8 := by decide +kernel
theorem rjStartRoot_rule : fragChecks rjStartRoot = onlyBroken 9 := by decide +kernel
theorem rjJoinRoot_rule : fragChecks rjJoinRoot = onlyBroken 9 := by decide +kernel
theorem rjSelfStart_rule : fragChecks rjSelfStart = onlyBroken 10 := by decide +kernel
theorem rjSelfJoin_rule : fragChecks rjSelfJoin = onlyBroken 10 := by decide +kernel
theorem rjTwoStarters_rule : fragChecks rjTwoStarters = onlyBroken 11 := by decide +kernel
theorem rjTwoStartersTry_rule : fragChecks rjTwoStartersTry = onlyBroken 11 := by
  decide +kernel
theorem rjTwoStarts_rule : fragChecks rjTwoStarts = onlyBroken 12 := by decide +kernel
theorem rjTwoStartsTry_rule : fragChecks rjTwoStartsTry = onlyBroken 12 := by decide +kernel

/-- Every rejected program is outside the fragment (from the `*_rule` theorems and
`fragB_eq`; also decided directly). -/
theorem rejected :
    fragB rjRootUndecl = false ∧ fragB rjStNotInj = false ∧ fragB rjStLock = false ∧
    fragB rjLockData = false ∧ fragB rjRdSt = false ∧ fragB rjWrLock = false ∧
    fragB rjWrSt = false ∧ fragB rjAsmLock = false ∧ fragB rjAsmSt = false ∧
    fragB rjStartUndecl = false ∧ fragB rjStartRoot = false ∧ fragB rjJoinRoot = false ∧
    fragB rjSelfStart = false ∧ fragB rjSelfJoin = false ∧ fragB rjTwoStarters = false ∧
    fragB rjTwoStartersTry = false ∧ fragB rjTwoStarts = false ∧
    fragB rjTwoStartsTry = false := by
  decide +kernel

/-- An accepted program with a `tryLock` that skips a `start` on failure (the path check
counts the `start` calls of the list, `maxStarts_eq_count`). -/
def okTryStart : LProg := mkP 1 [0] [0] fun | 0 => [.tryLock 0 2, .start 1, .unlock 0] | _ => []

theorem okTryStart_frag : fragB okTryStart = true := by decide +kernel

/-- The adequate bound of a program: `2·(longest code) + 3`. -/
def bnd (P : LProg) : ℕ := 2 * (P.threads.map (fun t => (P.code t).length)).foldl max 0 + 3

/-! ### Targets -/

theorem startNoJoin_target : fragB startNoJoin = true ∧ adequateB startNoJoin 5 = true ∧
    lifeTarget startNoJoin 5 =
      [2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem startJoin_target : fragB startJoin = true ∧ adequateB startJoin 7 = true ∧
    lifeTarget startJoin 7 =
      [3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem neverStarted_target : fragB neverStarted = true ∧ adequateB neverStarted 9 = true ∧
    lifeTarget neverStarted 9 =
      [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem joinThenStart_target : fragB joinThenStart = true ∧ adequateB joinThenStart 9 = true ∧
    lifeTarget joinThenStart 9 =
      [3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem raceJoin_target : fragB raceJoin = true ∧ adequateB raceJoin 7 = true ∧
    lifeTarget raceJoin 7 =
      [8, 0, 5, 0, 0, 0, 3, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem errStale_target : fragB errStale = true ∧ adequateB errStale 7 = true ∧
    lifeTarget errStale 7 =
      [2, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0] := by
  decide +kernel

theorem errTwo_target : fragB errTwo = true ∧ adequateB errTwo 7 = true ∧
    lifeTarget errTwo 7 =
      [4, 0, 3, 1, 0, 0, 0, 0, 1, 0, 0, 0] := by
  decide +kernel

theorem queryData_target : fragB queryData = true ∧ adequateB queryData 9 = true ∧
    lifeTarget queryData 9 =
      [4, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 3] := by
  decide +kernel

theorem asmRead_target : fragB asmRead = true ∧ adequateB asmRead 9 = true ∧
    lifeTarget asmRead 9 =
      [4, 0, 2, 0, 1, 0, 1, 0, 0, 1, 0, 1] := by
  decide +kernel

theorem asmLockRd_target : fragB asmLockRd = true ∧ adequateB asmLockRd 7 = true ∧
    lifeTarget asmLockRd 7 =
      [1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0] := by
  decide +kernel

theorem lockAcross_target : fragB lockAcross = true ∧ adequateB lockAcross 15 = true ∧
    lifeTarget lockAcross 15 =
      [2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0] := by
  decide +kernel

theorem joinErr_target : fragB joinErr = true ∧ adequateB joinErr 7 = true ∧
    lifeTarget joinErr 7 =
      [2, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0] := by
  decide +kernel

theorem workerStarts_target : fragB workerStarts = true ∧ adequateB workerStarts 9 = true ∧
    lifeTarget workerStarts 9 =
      [8, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem pubVis_target : fragB pubVis = true ∧ adequateB pubVis 11 = true ∧
    lifeTarget pubVis 11 =
      [3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem rptJoin_target : fragB rptJoin = true ∧ adequateB rptJoin 9 = true ∧
    lifeTarget rptJoin 9 =
      [3, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem nsHeld_target : fragB nsHeld = true ∧ adequateB nsHeld 5 = true ∧
    lifeTarget nsHeld 5 =
      [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem nsHeld2_target : fragB nsHeld2 = true ∧ adequateB nsHeld2 7 = true ∧
    lifeTarget nsHeld2 7 =
      [2, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0] := by
  decide +kernel

theorem queryRace_target : fragB queryRace = true ∧ adequateB queryRace 7 = true ∧
    lifeTarget queryRace 7 =
      [3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3] := by
  decide +kernel

theorem queryTry_target : fragB queryTry = true ∧ adequateB queryTry 11 = true ∧
    lifeTarget queryTry 11 =
      [8, 0, 2, 0, 0, 0, 6, 0, 0, 0, 0, 6] := by
  decide +kernel

theorem errFinal_target : fragB errFinal = true ∧ adequateB errFinal 13 = true ∧
    lifeTarget errFinal 13 =
      [8, 0, 7, 1, 0, 0, 0, 0, 1, 0, 0, 0] := by
  decide +kernel

theorem asmFinal_target : fragB asmFinal = true ∧ adequateB asmFinal 9 = true ∧
    lifeTarget asmFinal 9 =
      [4, 0, 3, 0, 1, 0, 0, 0, 0, 1, 0, 0] := by
  decide +kernel

theorem joinCycle_target : fragB joinCycle = true ∧ adequateB joinCycle 7 = true ∧
    lifeTarget joinCycle 7 =
      [7, 0, 5, 0, 0, 1, 1, 0, 0, 0, 1, 1] := by
  decide +kernel

theorem joinUnderLock_target : fragB joinUnderLock = true ∧ adequateB joinUnderLock 11 = true ∧
    lifeTarget joinUnderLock 11 =
      [5, 0, 3, 0, 0, 1, 1, 0, 0, 0, 1, 1] := by
  decide +kernel

theorem cutErr_target : fragB cutErr = true ∧ adequateB cutErr 2 = false ∧
    lifeTarget cutErr 2 =
      [2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem twoStarters_target : fragB twoStarters = true ∧ adequateB twoStarters 7 = true ∧
    lifeTarget twoStarters 7 =
      [10, 0, 8, 0, 0, 0, 2, 0, 0, 0, 0, 1] := by
  decide +kernel

end Life

end Condpor
