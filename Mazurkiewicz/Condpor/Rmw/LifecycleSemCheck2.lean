import Mazurkiewicz.Condpor.Rmw.LifecycleSemCheck

/-!
# Thread lifecycle machine: comparison on medium programs, merged enumeration (LC2-a)

As `LifecycleSemCheck.lean`, with `cmpM` (the merged enumeration `runsM`/`machSideM`) in
place of `cmp`: the plain enumeration of all maximal runs does not finish for these programs
(`twoStarters`: more than 120 s in the interpreter). `cmpM P n = (true, …)` says that the
set of serializations with classes of the graphs reached by `runsM` equals the `lifeSys`
side. That these are the graphs of all maximal runs rests on the claim of `runsM` (the key
determines all future graphs), which is not proved; `machSideM_small` in
`LifecycleSemCheck.lean` checks `machSideM = machSide` (as sets) on the small programs.

| program | bound | machine = `lifeSys` (error, blocked, deadlock, complete) |
|---|---|---|
| `twoStarters` | 7 | 0, 0, 0, 2 |
| `lateJoin` | 11 | 0, 0, 0, 1 |
| `reTry` | 15 | 0, 0, 0, 3 |
| `twoJoin` | 9 | 0, 0, 0, 4 |
| `twoFail` | 11 | 0, 0, 0, 7 |
| `asmStale` | 13 | 0, 2, 0, 1 |
| `lmin3` | 13 | 0, 0, 0, 2 |
| `lmin3e` | 11 | 0, 0, 0, 3 |
| `creator` | 15 | 0, 0, 0, 2 |
| `chain2` | 11 | 0, 0, 0, 3 |
-/

namespace Condpor

namespace Life

namespace Sem

theorem twoStarters_cmpM : cmpM twoStarters 7 = (true, [0, 0, 0, 2], [0, 0, 0, 2], 2) := by
  decide +kernel

theorem lateJoin_cmpM : cmpM lateJoin 11 = (true, [0, 0, 0, 1], [0, 0, 0, 1], 1) := by
  decide +kernel

theorem reTry_cmpM : cmpM reTry 15 = (true, [0, 0, 0, 3], [0, 0, 0, 3], 3) := by
  decide +kernel

theorem twoJoin_cmpM : cmpM twoJoin 9 = (true, [0, 0, 0, 4], [0, 0, 0, 4], 4) := by
  decide +kernel

theorem twoFail_cmpM : cmpM twoFail 11 = (true, [0, 0, 0, 7], [0, 0, 0, 7], 7) := by
  decide +kernel

theorem asmStale_cmpM : cmpM asmStale 13 = (true, [0, 2, 0, 1], [0, 2, 0, 1], 3) := by
  decide +kernel

theorem lmin3_cmpM : cmpM lmin3 13 = (true, [0, 0, 0, 2], [0, 0, 0, 2], 2) := by
  decide +kernel

theorem lmin3e_cmpM : cmpM lmin3e 11 = (true, [0, 0, 0, 3], [0, 0, 0, 3], 3) := by
  decide +kernel

theorem creator_cmpM : cmpM creator 15 = (true, [0, 0, 0, 2], [0, 0, 0, 2], 2) := by
  decide +kernel

theorem chain2_cmpM : cmpM chain2 11 = (true, [0, 0, 0, 3], [0, 0, 0, 3], 3) := by
  decide +kernel

end Sem

end Life

end Condpor
