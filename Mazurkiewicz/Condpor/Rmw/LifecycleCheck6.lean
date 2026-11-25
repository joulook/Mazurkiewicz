import Mazurkiewicz.Condpor.Rmw.LifecycleEx

/-!
# Thread lifecycle: a shrunk member of the J7 family

* `j7b` (from `j7`: worker `2` removed, the first joiner without its critical section).
  Expected before evaluation (the §5 machine of `opus-life-d4/machine.py`): 4 complete, 1
  signature. Evaluated: equal; 38 exploration.
-/

namespace Condpor

namespace Life

theorem j7b_target : fragB j7b = true ∧ adequateB j7b 15 = true ∧
    lifeTarget j7b 15 =
      [42, 0, 38, 0, 0, 0, 4, 0, 0, 0, 0, 1] := by
  decide +kernel

end Life

end Condpor
