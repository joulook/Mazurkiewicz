import Mazurkiewicz.Condpor.Rmw.LifecycleSemLemmas
-- Imported only to make the build sequential (memory): see LifecycleCheck2.
import Mazurkiewicz.Condpor.Rmw.LifecycleCheck6
import Mazurkiewicz.Condpor.Rmw.LifecycleEx

/-!
# Thread lifecycle machine: kernel-checked comparison with `lifeSys` (LC2-a)

For each program of `LifecycleEx.lean` below, at its adequate bound, by `decide +kernel`:
the program is in the fragment, the bound is adequate, and
`cmp P n = (true, m, l, k)`:

* `true`: the set of pairs (serialization `ser` of the graph, class) over all maximal runs of
  the machine (`machSide`, from the enumeration `machRuns`, which lists exactly the maximal
  runs: `mem_machRuns_iff`) equals the set of pairs (serialization, `lifeClass`) over the
  terminal-valid configurations of the explorer (`lifeSide`); `cmp_spec` turns this into
  the two inclusions on runs and explorer configurations;
* `m`, `l`: the class counts (error, blocked, deadlock, complete) of the two sides (`m`
  after removing repetitions);
* `k`: the number of distinct serializations on the `lifeSys` side (= the number of its
  terminal-valid graphs, so the serialization separates them).

What is compared: full graphs. `ser` lists, per thread, every event (thread, index, label)
with its `rf` value, and the coherence order of every written location; the initial memory
is `lifeMem P` on both sides (by construction of `GB.toCfg`, and `mem_eq` for executions of
`lifeSys`), and there are no constraint evaluations.

| program | bound | machine = `lifeSys` (error, blocked, deadlock, complete) |
|---|---|---|
| `startNoJoin` | 5 | 0, 0, 0, 1 |
| `startJoin` | 7 | 0, 0, 0, 1 |
| `neverStarted` | 9 | 0, 0, 0, 1 |
| `joinThenStart` | 9 | 0, 0, 0, 1 |
| `raceJoin` | 7 | 0, 0, 0, 3 |
| `errStale` | 7 | 1, 0, 0, 0 |
| `errTwo` | 7 | 1, 0, 0, 0 |
| `queryData` | 9 | 0, 0, 0, 3 |
| `asmRead` | 9 | 0, 1, 0, 1 |
| `asmLockRd` | 7 | 0, 1, 0, 0 |
| `lockAcross` | 15 | 0, 0, 1, 0 |
| `joinErr` | 7 | 1, 0, 0, 0 |
| `workerStarts` | 9 | 0, 0, 0, 2 |
| `pubVis` | 11 | 0, 0, 0, 1 |
| `rptJoin` | 9 | 0, 0, 0, 1 |
| `nsHeld` | 5 | 0, 0, 0, 1 |
| `nsHeld2` | 7 | 0, 0, 1, 0 |
| `queryRace` | 7 | 0, 0, 0, 3 |
| `queryTry` | 11 | 0, 0, 0, 6 |
| `errFinal` | 13 | 1, 0, 0, 0 |
| `asmFinal` | 9 | 0, 1, 0, 0 |
| `joinCycle` | 7 | 0, 0, 1, 1 |
| `joinUnderLock` | 11 | 0, 0, 1, 1 |

Categories asked for: join before start (`joinThenStart`), join cycle (`joinCycle`), error
(`errStale`, `errTwo`, `joinErr`, `errFinal`), failing assume (`asmRead`, `asmLockRd`,
`asmFinal`), never-started thread (`neverStarted`, `nsHeld`), reentrant lock
(`lockAcross`), `tryLock` (`queryTry`), lock query (`queryData`, `queryRace`, `queryTry`).

`machSideM_small`: on these programs the merged enumeration (`machSideM`) gives the same set
as the plain one (`machSide`).
-/

namespace Condpor

namespace Life

namespace Sem

theorem startNoJoin_cmp : fragB startNoJoin = true ∧ adequateB startNoJoin 5 = true ∧
    cmp startNoJoin 5 = (true, [0, 0, 0, 1], [0, 0, 0, 1], 1) := by
  decide +kernel

theorem startJoin_cmp : fragB startJoin = true ∧ adequateB startJoin 7 = true ∧
    cmp startJoin 7 = (true, [0, 0, 0, 1], [0, 0, 0, 1], 1) := by
  decide +kernel

theorem neverStarted_cmp : fragB neverStarted = true ∧ adequateB neverStarted 9 = true ∧
    cmp neverStarted 9 = (true, [0, 0, 0, 1], [0, 0, 0, 1], 1) := by
  decide +kernel

theorem joinThenStart_cmp : fragB joinThenStart = true ∧ adequateB joinThenStart 9 = true ∧
    cmp joinThenStart 9 = (true, [0, 0, 0, 1], [0, 0, 0, 1], 1) := by
  decide +kernel

theorem raceJoin_cmp : fragB raceJoin = true ∧ adequateB raceJoin 7 = true ∧
    cmp raceJoin 7 = (true, [0, 0, 0, 3], [0, 0, 0, 3], 3) := by
  decide +kernel

theorem errStale_cmp : fragB errStale = true ∧ adequateB errStale 7 = true ∧
    cmp errStale 7 = (true, [1, 0, 0, 0], [1, 0, 0, 0], 1) := by
  decide +kernel

theorem errTwo_cmp : fragB errTwo = true ∧ adequateB errTwo 7 = true ∧
    cmp errTwo 7 = (true, [1, 0, 0, 0], [1, 0, 0, 0], 1) := by
  decide +kernel

theorem queryData_cmp : fragB queryData = true ∧ adequateB queryData 9 = true ∧
    cmp queryData 9 = (true, [0, 0, 0, 3], [0, 0, 0, 3], 3) := by
  decide +kernel

theorem asmRead_cmp : fragB asmRead = true ∧ adequateB asmRead 9 = true ∧
    cmp asmRead 9 = (true, [0, 1, 0, 1], [0, 1, 0, 1], 2) := by
  decide +kernel

theorem asmLockRd_cmp : fragB asmLockRd = true ∧ adequateB asmLockRd 7 = true ∧
    cmp asmLockRd 7 = (true, [0, 1, 0, 0], [0, 1, 0, 0], 1) := by
  decide +kernel

theorem lockAcross_cmp : fragB lockAcross = true ∧ adequateB lockAcross 15 = true ∧
    cmp lockAcross 15 = (true, [0, 0, 1, 0], [0, 0, 1, 0], 1) := by
  decide +kernel

theorem joinErr_cmp : fragB joinErr = true ∧ adequateB joinErr 7 = true ∧
    cmp joinErr 7 = (true, [1, 0, 0, 0], [1, 0, 0, 0], 1) := by
  decide +kernel

theorem workerStarts_cmp : fragB workerStarts = true ∧ adequateB workerStarts 9 = true ∧
    cmp workerStarts 9 = (true, [0, 0, 0, 2], [0, 0, 0, 2], 2) := by
  decide +kernel

theorem pubVis_cmp : fragB pubVis = true ∧ adequateB pubVis 11 = true ∧
    cmp pubVis 11 = (true, [0, 0, 0, 1], [0, 0, 0, 1], 1) := by
  decide +kernel

theorem rptJoin_cmp : fragB rptJoin = true ∧ adequateB rptJoin 9 = true ∧
    cmp rptJoin 9 = (true, [0, 0, 0, 1], [0, 0, 0, 1], 1) := by
  decide +kernel

theorem nsHeld_cmp : fragB nsHeld = true ∧ adequateB nsHeld 5 = true ∧
    cmp nsHeld 5 = (true, [0, 0, 0, 1], [0, 0, 0, 1], 1) := by
  decide +kernel

theorem nsHeld2_cmp : fragB nsHeld2 = true ∧ adequateB nsHeld2 7 = true ∧
    cmp nsHeld2 7 = (true, [0, 0, 1, 0], [0, 0, 1, 0], 1) := by
  decide +kernel

theorem queryRace_cmp : fragB queryRace = true ∧ adequateB queryRace 7 = true ∧
    cmp queryRace 7 = (true, [0, 0, 0, 3], [0, 0, 0, 3], 3) := by
  decide +kernel

theorem queryTry_cmp : fragB queryTry = true ∧ adequateB queryTry 11 = true ∧
    cmp queryTry 11 = (true, [0, 0, 0, 6], [0, 0, 0, 6], 6) := by
  decide +kernel

theorem errFinal_cmp : fragB errFinal = true ∧ adequateB errFinal 13 = true ∧
    cmp errFinal 13 = (true, [1, 0, 0, 0], [1, 0, 0, 0], 1) := by
  decide +kernel

theorem asmFinal_cmp : fragB asmFinal = true ∧ adequateB asmFinal 9 = true ∧
    cmp asmFinal 9 = (true, [0, 1, 0, 0], [0, 1, 0, 0], 1) := by
  decide +kernel

theorem joinCycle_cmp : fragB joinCycle = true ∧ adequateB joinCycle 7 = true ∧
    cmp joinCycle 7 = (true, [0, 0, 1, 1], [0, 0, 1, 1], 2) := by
  decide +kernel

theorem joinUnderLock_cmp : fragB joinUnderLock = true ∧ adequateB joinUnderLock 11 = true ∧
    cmp joinUnderLock 11 = (true, [0, 0, 1, 1], [0, 0, 1, 1], 2) := by
  decide +kernel

theorem machSideM_small :
    [startNoJoin, startJoin, neverStarted, joinThenStart, raceJoin, errStale, errTwo, queryData,
      asmRead, asmLockRd, lockAcross, joinErr, workerStarts, pubVis, rptJoin, nsHeld, nsHeld2,
      queryRace, queryTry, errFinal, asmFinal, joinCycle, joinUnderLock].all
      (fun P => sameSet (machSideM P) (machSide P)) = true := by
  decide +kernel

end Sem

end Life

end Condpor
