import Mazurkiewicz.Condpor.Rmw.LifecycleEx

/-!
# Thread lifecycle: `dl2` and `tryjoin2`

* `dl2`: two workers taking two locks in opposite orders, both joined. Expected (d1 dump,
  `proj.py`): 2 complete, 1 deadlock, 14 exploration; signatures 2 complete, 1 deadlock.
  Evaluated: equal.
* `tryjoin2`: the tryjoin family without its plain worker: `1: join 2; tryLock; unlock`,
  `2: lock; unlock; tryLock; unlock`. Expected (the §5 machine of `opus-life-d4`, run by
  the implementer): 7 complete, 6 signatures. Evaluated: equal; 21 exploration.

The full tryjoin, chain, diamond and J7 are defined in `LifecycleEx.lean` but not
evaluated in any CI-built file. Their numbers come from runs outside LC1's Lean files: the
d1 hand-encoding dump with `proj.py` for tryjoin (239 full, 36 complete, 29 signatures), the
brute force and the §5 machine for chain (52 complete / 24 signatures), diamond (56 / 24) and
J7 (48 / 12). LC1's own external runs (interpreter, not theorems) are logged in
`/local/home/mkhoshechin/tmp/rmw-review/lc1-external/`.
-/

namespace Condpor

namespace Life

theorem dl2_target : fragB dl2 = true ∧ adequateB dl2 11 = true ∧
    lifeTarget dl2 11 =
      [17, 0, 14, 0, 0, 1, 2, 0, 0, 0, 1, 2] := by
  decide +kernel

theorem tryjoin2_target : fragB tryjoin2 = true ∧ adequateB tryjoin2 11 = true ∧
    lifeTarget tryjoin2 11 =
      [28, 0, 21, 0, 0, 0, 7, 0, 0, 0, 0, 6] := by
  decide +kernel

end Life

end Condpor
