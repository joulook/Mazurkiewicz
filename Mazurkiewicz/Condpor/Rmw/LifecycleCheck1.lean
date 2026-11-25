import Mazurkiewicz.Condpor.Rmw.LifecycleEx

/-!
# Thread lifecycle: targets of medium size

Kernel-evaluated targets as in `LifecycleEx.lean` (same statement shape).

| program | expected (source) | evaluated |
|---|---|---|
| `lateJoin` | 1 compl, 4 expl, sig 1 (d1, sig) | equal |
| `reTry` | 3 compl, 5 expl (d3) | equal |
| `twoJoin` | 4 compl, 21 expl, sig 1 (d2, sig) | equal |
| `twoFail` | 7 compl, 5 expl (d3) | equal |
| `asmStale` | 2 blocked, 1 compl, 8 expl (d3) | equal |
| `lmin3` | 2 compl, 13 expl, sig 2 (d1, sig) | equal |
| `lmin3e` | 3 compl, 13 expl, sig 3 (d1, sig) | equal |
| `creator` | 2 compl, 14 expl, sig 2 (d1, sig) | equal |
| `chain2` | 3 compl, sig 2 (mach; the chain family with two workers) | equal; 14 expl |
-/

namespace Condpor

namespace Life

theorem lateJoin_target : fragB lateJoin = true ∧ adequateB lateJoin 11 = true ∧
    lifeTarget lateJoin 11 =
      [5, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem reTry_target : fragB reTry = true ∧ adequateB reTry 15 = true ∧
    lifeTarget reTry 15 =
      [8, 0, 5, 0, 0, 0, 3, 0, 0, 0, 0, 3] := by
  decide +kernel

theorem twoJoin_target : fragB twoJoin = true ∧ adequateB twoJoin 9 = true ∧
    lifeTarget twoJoin 9 =
      [25, 0, 21, 0, 0, 0, 4, 0, 0, 0, 0, 1] := by
  decide +kernel

theorem twoFail_target : fragB twoFail = true ∧ adequateB twoFail 11 = true ∧
    lifeTarget twoFail 11 =
      [12, 0, 5, 0, 0, 0, 7, 0, 0, 0, 0, 7] := by
  decide +kernel

theorem asmStale_target : fragB asmStale = true ∧ adequateB asmStale 13 = true ∧
    lifeTarget asmStale 13 =
      [11, 0, 8, 0, 2, 0, 1, 0, 0, 2, 0, 1] := by
  decide +kernel

theorem lmin3_target : fragB lmin3 = true ∧ adequateB lmin3 13 = true ∧
    lifeTarget lmin3 13 =
      [15, 0, 13, 0, 0, 0, 2, 0, 0, 0, 0, 2] := by
  decide +kernel

theorem lmin3e_target : fragB lmin3e = true ∧ adequateB lmin3e 11 = true ∧
    lifeTarget lmin3e 11 =
      [16, 0, 13, 0, 0, 0, 3, 0, 0, 0, 0, 3] := by
  decide +kernel

theorem creator_target : fragB creator = true ∧ adequateB creator 15 = true ∧
    lifeTarget creator 15 =
      [16, 0, 14, 0, 0, 0, 2, 0, 0, 0, 0, 2] := by
  decide +kernel

theorem chain2_target : fragB chain2 = true ∧ adequateB chain2 11 = true ∧
    lifeTarget chain2 11 =
      [17, 0, 14, 0, 0, 0, 3, 0, 0, 0, 0, 2] := by
  decide +kernel

end Life

end Condpor
