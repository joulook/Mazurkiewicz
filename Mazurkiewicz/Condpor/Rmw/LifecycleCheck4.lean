import Mazurkiewicz.Condpor.Rmw.LifecycleEx
-- Not imported from the root file: checking this module needs about 15 GB, more than the CI
-- runner has. Build on demand: `lake build Mazurkiewicz.Condpor.Rmw.LifecycleCheck4`.

/-!
# Thread lifecycle: `dl2j` (a joiner of deadlocked threads)

`dl2` with a third worker `3: join 1` (the design's `joinDead`). Expected: 48 full graphs
(d1 dump), 2 complete, 1 deadlock, 45 exploration, signatures 1 deadlock and 2 complete
(d1 dump and `proj.py`; Opus LC1-r1 `#eval`: `[48, 0, 45, 0, 0, 1, 2, 0, 0, 0, 1, 2]`).
Evaluated by the kernel: equal.
-/

namespace Condpor

namespace Life

theorem dl2j_target : fragB dl2j = true ∧ adequateB dl2j 15 = true ∧
    lifeTarget dl2j 15 =
      [48, 0, 45, 0, 0, 1, 2, 0, 0, 0, 1, 2] := by
  decide +kernel

end Life

end Condpor
