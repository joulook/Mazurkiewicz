import Mazurkiewicz.Condpor.Rmw.TargetsEx

/-! Reference outputs for JMC: kernel check of the class counts of T15, reversed order. -/

namespace Condpor

namespace Targets

theorem counts_T15_rev :
    classCounts [0,1,2] (exploreCfgAtF (mkL T15c.reverse 12) 12) = (30,0,0,0,32) := by
  decide +kernel

end Targets

end Condpor
