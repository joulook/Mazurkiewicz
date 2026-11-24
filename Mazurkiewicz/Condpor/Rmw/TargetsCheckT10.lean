import Mazurkiewicz.Condpor.Rmw.TargetsEx

/-! Reference outputs for JMC: kernel check of the class counts of T10, reversed order. -/

namespace Condpor

namespace Targets

theorem counts_T10_rev :
    classCounts [0,1] (exploreCfgAtF (mkL T10c.reverse 12) 12) = (15,0,0,0,6) := by
  decide +kernel

end Targets

end Condpor
