import Mazurkiewicz.Condpor.Rmw.TargetsEx

/-!
# Reference outputs for JMC: kernel checks of class counts (second group)

As `TargetsCheck.lean`, for L2, L4, L5, L8, T7, T8, T9 in both thread orders.
The tuples are (complete, dropped, bound, deadlock, exploration).
-/

namespace Condpor

namespace Targets

theorem counts_L2_fwd : classCounts [0, 1, 2] (exploreCfgAtF (mkL L2c 6) 6) = (6, 0, 0, 0, 15) := by
  decide +kernel

theorem counts_L2_rev : classCounts [0, 1, 2] (exploreCfgAtF (mkL L2c.reverse 6) 6) = (6, 0, 0, 0, 15) := by
  decide +kernel

theorem counts_L4_fwd : classCounts [0, 1, 2] (exploreCfgAtF (mkL L4c 6) 6) = (6, 0, 0, 3, 4) := by
  decide +kernel

theorem counts_L4_rev : classCounts [0, 1, 2] (exploreCfgAtF (mkL L4c.reverse 6) 6) = (6, 0, 0, 3, 4) := by
  decide +kernel

theorem counts_L5_fwd : classCounts [0, 1] (exploreCfgAtF (mkL L5c 12) 12) = (2, 0, 0, 1, 4) := by
  decide +kernel

theorem counts_L5_rev : classCounts [0, 1] (exploreCfgAtF (mkL L5c.reverse 12) 12) = (2, 0, 0, 1, 4) := by
  decide +kernel

theorem counts_L8_fwd : classCounts [0, 1, 2] (exploreCfgAtF (mkL L8c 9) 9) = (4, 0, 0, 0, 3) := by
  decide +kernel

theorem counts_L8_rev : classCounts [0, 1, 2] (exploreCfgAtF (mkL L8c.reverse 9) 9) = (4, 0, 0, 0, 3) := by
  decide +kernel

theorem counts_T7_fwd : classCounts [0, 1, 2] (exploreCfgAtF (progT7) 9) = (21, 0, 0, 0, 0) := by
  decide +kernel

theorem counts_T7_rev : classCounts [0, 1, 2] (exploreCfgAtF (mkL T7c.reverse 9) 9) = (21, 0, 0, 0, 0) := by
  decide +kernel

theorem counts_T8_fwd : classCounts [0, 1, 2] (exploreCfgAtF (progT8) 9) = (10, 0, 0, 0, 11) := by
  decide +kernel

theorem counts_T8_rev : classCounts [0, 1, 2] (exploreCfgAtF (mkL T8c.reverse 9) 9) = (10, 0, 0, 0, 11) := by
  decide +kernel

theorem counts_T9_fwd : classCounts [0, 1, 2] (exploreCfgAtF (progT9) 9) = (15, 0, 0, 0, 6) := by
  decide +kernel

theorem counts_T9_rev : classCounts [0, 1, 2] (exploreCfgAtF (mkL T9c.reverse 9) 9) = (15, 0, 0, 0, 6) := by
  decide +kernel

end Targets

end Condpor
