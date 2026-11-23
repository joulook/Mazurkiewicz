import Mazurkiewicz.Condpor.Rmw.TargetsEx

/-!
# Reference outputs for JMC: kernel checks, round 2

* L9 (design I.6): in every full graph, every read of the lock location made
  while its thread holds the lock (`isHolderQuery`) reads its own thread's last
  write of the lock, and that write is exclusive (`WX`); there are 13 such
  reads over the 16 graphs (the check is not vacuous). Both orders.
* L9b: class counts, both orders; it has no holder's query.
* The cut: for L1, L3, L7 and L10 (forward order) the listings with the cut
  `n + 1` are exactly those with the cut `n` (same graphs, same order).

The location lists are written as literals (`[0]`, `[0, 1]`): they are
`lockLocs`/`allLocs` of the code, whose `mergeSort` the kernel does not reduce.
-/

namespace Condpor

namespace Targets

theorem holder_L9_fwd :
    (exploreCfgAtF (mkL L9c 9) 9).all (holderOkB (mkL L9c 9) L9c [0]) = true ∧
      ((exploreCfgAtF (mkL L9c 9) 9).map (holderCount L9c [0])).sum = 13 := by
  decide +kernel

theorem holder_L9_rev :
    (exploreCfgAtF (mkL L9c.reverse 9) 9).all (holderOkB (mkL L9c.reverse 9) L9c.reverse [0]) =
        true ∧
      ((exploreCfgAtF (mkL L9c.reverse 9) 9).map (holderCount L9c.reverse [0])).sum = 13 := by
  decide +kernel

theorem counts_L9b_fwd : classCounts [0, 1, 2] (exploreCfgAtF (mkL L9bc 9) 9) = (10, 0, 0, 0, 6) := by
  decide +kernel

theorem counts_L9b_rev :
    classCounts [0, 1, 2] (exploreCfgAtF (mkL L9bc.reverse 9) 9) = (10, 0, 0, 0, 6) := by
  decide +kernel

theorem holder_L9b :
    ((exploreCfgAtF (mkL L9bc 9) 9).map (holderCount L9bc [0])).sum = 0 ∧
      ((exploreCfgAtF (mkL L9bc.reverse 9) 9).map (holderCount L9bc.reverse [0])).sum = 0 := by
  decide +kernel

theorem cut_L1 : (exploreCfgAtF (mkL L1c 7) 7).map (rawOf (mkL L1c 7) [0, 1] [0]) =
    (exploreCfgAtF progT0 6).map (rawOf progT0 [0, 1] [0]) := by
  decide +kernel

theorem cut_L3 : (exploreCfgAtF (mkL L3c 7) 7).map (rawOf (mkL L3c 7) [0, 1] [0]) =
    (exploreCfgAtF progT17 6).map (rawOf progT17 [0, 1] [0]) := by
  decide +kernel

theorem cut_L7 : (exploreCfgAtF (mkL L7c 7) 7).map (rawOf (mkL L7c 7) [0, 1] [0]) =
    (exploreCfgAtF progT4 6).map (rawOf progT4 [0, 1] [0]) := by
  decide +kernel

theorem cut_L10 : (exploreCfgAtF (mkL L10c 13) 13).map (rawOf (mkL L10c 13) [0, 1] [0, 1]) =
    (exploreCfgAtF (mkL L10c 12) 12).map (rawOf (mkL L10c 12) [0, 1] [0, 1]) := by
  decide +kernel

end Targets

end Condpor
