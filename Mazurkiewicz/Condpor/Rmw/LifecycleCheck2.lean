import Mazurkiewicz.Condpor.Rmw.LifecycleEx

/-!
# Thread lifecycle: `lowChild`

The child `2` started by main starts the child `1` of lower id. Expected (d1 dump, `proj.py`):
6 complete, 38 exploration, 6 signatures. Evaluated: equal. (In `lowChild` all 6
terminal-valid graphs are reached only through a revisit of a start-read, §6.1.)
-/

namespace Condpor

namespace Life

theorem lowChild_target : fragB lowChild = true ∧ adequateB lowChild 13 = true ∧
    lifeTarget lowChild 13 =
      [44, 0, 38, 0, 0, 0, 6, 0, 0, 0, 0, 6] := by
  decide +kernel

end Life

end Condpor
