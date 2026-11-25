import Mazurkiewicz.Condpor.Rmw.LifecycleEx
-- Not imported from the root file: checking this module needs about 15 GB, more than the CI
-- runner has. Build on demand: `lake build Mazurkiewicz.Condpor.Rmw.LifecycleCheck5`.

/-!
# Thread lifecycle: a shrunk member of the diamond family

* `diamondB` (from `diamond`: worker `4` removed, the second joiner without its critical
  section). Expected before evaluation (the §5 machine of `opus-life-d4/machine.py`): 6
  complete, 2 signatures. Evaluated: equal; 58 exploration.
-/

namespace Condpor

namespace Life

theorem diamondB_target : fragB diamondB = true ∧ adequateB diamondB 15 = true ∧
    lifeTarget diamondB 15 =
      [64, 0, 58, 0, 0, 0, 6, 0, 0, 0, 0, 2] := by
  decide +kernel

end Life

end Condpor
