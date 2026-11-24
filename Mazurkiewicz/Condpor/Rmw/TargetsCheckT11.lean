import Mazurkiewicz.Condpor.Rmw.TargetsEx

/-! Reference outputs for JMC: kernel check of the class counts of T11, reversed order. -/

namespace Condpor

namespace Targets

theorem counts_T11_rev :
    classCounts [0,1,2] (exploreCfgAtF (mkL T11c.reverse 12) 12) = (44,0,0,0,18) := by
  decide +kernel

end Targets

end Condpor
