import Mazurkiewicz.Condpor.Rmw.TargetsEx

/-! Reference outputs for JMC: kernel check of the class counts of T13, reversed order. -/

namespace Condpor

namespace Targets

theorem counts_T13_rev :
    classCounts [0,1] (exploreCfgAtF (mkL T13c.reverse 12) 12) = (26,0,0,0,0) := by
  decide +kernel

end Targets

end Condpor
