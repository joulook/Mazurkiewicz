import Mazurkiewicz.Condpor.Rmw.TargetsEx

/-!
# Reference outputs for JMC: kernel checks

The class counts of the smaller programs of `TargetsEx.lean` and the complete
raw listings (events, `rf`, values, insertion order, coherence, blocked
threads, class) of L1, L3 (both orders) and L10 (forward order), checked by the
kernel on `exploreCfgAtF` (which is `exploreCfgAt P oracleC n`,
`exploreCfgAtF_eq`, whose graphs are `exploreAt P eqOracleSe n`,
`exploreCfgAtF_abs`). The JSON files are printed from the same data by
`writeAll`; the literals below were produced by it and pasted.

The tuples are (complete, dropped, bound, deadlock, exploration).
-/

set_option linter.style.longLine false

namespace Condpor

namespace Targets

open Program

theorem counts_L1_fwd : classCounts [0, 1] (exploreCfgAtF (progT0) 6) = (2, 0, 0, 0, 2) := by
  decide +kernel

theorem counts_L1_rev : classCounts [0, 1] (exploreCfgAtF (mkL L1c.reverse 6) 6) = (2, 0, 0, 0, 2) := by
  decide +kernel

theorem counts_L3_fwd : classCounts [0, 1] (exploreCfgAtF (progT17) 6) = (1, 0, 0, 1, 1) := by
  decide +kernel

theorem counts_L3_rev : classCounts [0, 1] (exploreCfgAtF (mkL L3c.reverse 6) 6) = (1, 0, 0, 1, 1) := by
  decide +kernel

theorem counts_L7_fwd : classCounts [0, 1] (exploreCfgAtF (progT4) 6) = (2, 0, 0, 0, 2) := by
  decide +kernel

theorem counts_L7_rev : classCounts [0, 1] (exploreCfgAtF (mkL L7c.reverse 6) 6) = (2, 0, 0, 0, 2) := by
  decide +kernel

theorem counts_L9_fwd : classCounts [0, 1, 2] (exploreCfgAtF (mkL L9c 9) 9) = (10, 0, 0, 0, 6) := by
  decide +kernel

theorem counts_L9_rev : classCounts [0, 1, 2] (exploreCfgAtF (mkL L9c.reverse 9) 9) = (10, 0, 0, 0, 6) := by
  decide +kernel

theorem counts_L10_fwd : classCounts [0, 1] (exploreCfgAtF (mkL L10c 12) 12) = (4, 0, 0, 0, 3) := by
  decide +kernel

theorem counts_L10_rev : classCounts [0, 1] (exploreCfgAtF (mkL L10c.reverse 12) 12) = (4, 0, 0, 0, 3) := by
  decide +kernel

theorem counts_T12_fwd : classCounts [0, 1] (exploreCfgAtF (progT12) 9) = (4, 0, 0, 0, 4) := by
  decide +kernel

theorem counts_T12_rev : classCounts [0, 1] (exploreCfgAtF (mkL T12c.reverse 9) 9) = (4, 0, 0, 0, 4) := by
  decide +kernel

/-- The listing of L1 fwd. -/
theorem listing_L1_fwd :
    (exploreCfgAtF (progT0) 6).map (rawOf (progT0) (List.range (L1c).length) (allLocs (L1c))) =
      [{ evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (1, 1)), phi := 0 },
                 { t := 0, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (1, 0), (1, 1), (0, 1), (1, 2)],
         co := [(0, [(1, 1), (1, 2)])],
         blocked := [0],
         cls := Condpor.Targets.Cls.exploration },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some (some (1, 2)), phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (1, 0), (1, 1), (1, 2), (0, 1), (0, 2)],
         co := [(0, [(1, 1), (1, 2), (0, 1), (0, 2)])],
         blocked := [],
         cls := Condpor.Targets.Cls.complete },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some (some (0, 2)), phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)],
         co := [(0, [(0, 1), (0, 2), (1, 1), (1, 2)])],
         blocked := [],
         cls := Condpor.Targets.Cls.complete },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (0, 1)), phi := 0 },
                 { t := 1, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)],
         co := [(0, [(0, 1), (0, 2)])],
         blocked := [1],
         cls := Condpor.Targets.Cls.exploration }]
    := by
  decide +kernel

/-- The listing of L1 rev. -/
theorem listing_L1_rev :
    (exploreCfgAtF (mkL L1c.reverse 6) 6).map (rawOf (mkL L1c.reverse 6) (List.range (L1c.reverse).length) (allLocs (L1c.reverse))) =
      [{ evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (1, 1)), phi := 0 },
                 { t := 0, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (1, 0), (1, 1), (0, 1), (1, 2)],
         co := [(0, [(1, 1), (1, 2)])],
         blocked := [0],
         cls := Condpor.Targets.Cls.exploration },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some (some (1, 2)), phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (1, 0), (1, 1), (1, 2), (0, 1), (0, 2)],
         co := [(0, [(1, 1), (1, 2), (0, 1), (0, 2)])],
         blocked := [],
         cls := Condpor.Targets.Cls.complete },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some (some (0, 2)), phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)],
         co := [(0, [(0, 1), (0, 2), (1, 1), (1, 2)])],
         blocked := [],
         cls := Condpor.Targets.Cls.complete },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (0, 1)), phi := 0 },
                 { t := 1, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)],
         co := [(0, [(0, 1), (0, 2)])],
         blocked := [1],
         cls := Condpor.Targets.Cls.exploration }]
    := by
  decide +kernel

/-- The listing of L3 fwd. -/
theorem listing_L3_fwd :
    (exploreCfgAtF (progT17) 6).map (rawOf (progT17) (List.range (L3c).length) (allLocs (L3c))) =
      [{ evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (1, 1)), phi := 0 },
                 { t := 0, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 }],
         order := [(0, 0), (1, 0), (1, 1), (0, 1)],
         co := [(0, [(1, 1)])],
         blocked := [0],
         cls := Condpor.Targets.Cls.deadlock },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some (some (0, 2)), phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)],
         co := [(0, [(0, 1), (0, 2), (1, 1)])],
         blocked := [],
         cls := Condpor.Targets.Cls.complete },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (0, 1)), phi := 0 },
                 { t := 1, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1)],
         co := [(0, [(0, 1), (0, 2)])],
         blocked := [1],
         cls := Condpor.Targets.Cls.exploration }]
    := by
  decide +kernel

/-- The listing of L3 rev. -/
theorem listing_L3_rev :
    (exploreCfgAtF (mkL L3c.reverse 6) 6).map (rawOf (mkL L3c.reverse 6) (List.range (L3c.reverse).length) (allLocs (L3c.reverse))) =
      [{ evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (1, 1)), phi := 0 },
                 { t := 0, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (1, 0), (1, 1), (0, 1), (1, 2)],
         co := [(0, [(1, 1), (1, 2)])],
         blocked := [0],
         cls := Condpor.Targets.Cls.exploration },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some (some (1, 2)), phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (1, 0), (1, 1), (1, 2), (0, 1)],
         co := [(0, [(1, 1), (1, 2), (0, 1)])],
         blocked := [],
         cls := Condpor.Targets.Cls.complete },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (0, 1)), phi := 0 },
                 { t := 1, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (1, 0), (1, 1)],
         co := [(0, [(0, 1)])],
         blocked := [1],
         cls := Condpor.Targets.Cls.deadlock }]
    := by
  decide +kernel

/-- The listing of L10 fwd. -/
theorem listing_L10_fwd :
    (exploreCfgAtF (mkL L10c 12) 12).map (rawOf (mkL L10c 12) [0, 1] [0, 1]) =
      [{ evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (1, 1)), phi := 0 },
                 { t := 0, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 0, loc := 1, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 3, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (1, 0), (1, 1), (0, 1), (1, 2), (1, 3)],
         co := [(0, [(1, 1), (1, 3)]), (1, [])],
         blocked := [0],
         cls := Condpor.Targets.Cls.exploration },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some (some (1, 3)), phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 4, loc := 0, val := 1, rf := none, phi := 1 },
                 { t := 0, i := 3, kind := 1, loc := 1, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 4, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 0, loc := 1, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 3, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (1, 0), (1, 1), (1, 2), (1, 3), (0, 1), (0, 2), (0, 3), (0, 4)],
         co := [(0, [(1, 1), (1, 3), (0, 1), (0, 4)]), (1, [(0, 3)])],
         blocked := [],
         cls := Condpor.Targets.Cls.complete },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some (some (1, 3)), phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 4, loc := 0, val := 0, rf := none, phi := 1 },
                 { t := 0, i := 3, kind := 1, loc := 1, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 4, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 0, loc := 1, val := 0, rf := some none, phi := 0 },
                 { t := 1, i := 3, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (1, 0), (1, 1), (1, 2), (1, 3), (0, 1), (0, 2), (0, 3), (0, 4)],
         co := [(0, [(1, 1), (1, 3), (0, 1), (0, 4)]), (1, [(0, 3)])],
         blocked := [],
         cls := Condpor.Targets.Cls.complete },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 4, loc := 0, val := 1, rf := none, phi := 1 },
                 { t := 0, i := 3, kind := 1, loc := 1, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 4, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some (some (0, 4)), phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 0, loc := 1, val := 1, rf := some (some (0, 3)), phi := 0 },
                 { t := 1, i := 3, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3)],
         co := [(0, [(0, 1), (0, 4), (1, 1), (1, 3)]), (1, [(0, 3)])],
         blocked := [],
         cls := Condpor.Targets.Cls.complete },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 4, loc := 0, val := 1, rf := none, phi := 1 },
                 { t := 0, i := 3, kind := 1, loc := 1, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 4, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (0, 1)), phi := 0 },
                 { t := 1, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1)],
         co := [(0, [(0, 1), (0, 4)]), (1, [(0, 3)])],
         blocked := [1],
         cls := Condpor.Targets.Cls.exploration },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 4, loc := 0, val := 0, rf := none, phi := 1 },
                 { t := 0, i := 3, kind := 1, loc := 1, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 4, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 0, rf := some (some (0, 4)), phi := 0 },
                 { t := 1, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 1, i := 2, kind := 0, loc := 1, val := 1, rf := some (some (0, 3)), phi := 0 },
                 { t := 1, i := 3, kind := 1, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3)],
         co := [(0, [(0, 1), (0, 4), (1, 1), (1, 3)]), (1, [(0, 3)])],
         blocked := [],
         cls := Condpor.Targets.Cls.complete },
       { evs := [{ t := 0, i := 0, kind := 2, loc := 0, val := 0, rf := some none, phi := 0 },
                 { t := 0, i := 1, kind := 3, loc := 0, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 2, kind := 4, loc := 0, val := 0, rf := none, phi := 1 },
                 { t := 0, i := 3, kind := 1, loc := 1, val := 1, rf := none, phi := 0 },
                 { t := 0, i := 4, kind := 1, loc := 0, val := 0, rf := none, phi := 0 },
                 { t := 1, i := 0, kind := 2, loc := 0, val := 1, rf := some (some (0, 1)), phi := 0 },
                 { t := 1, i := 1, kind := 5, loc := 0, val := 0, rf := none, phi := 0 }],
         order := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1)],
         co := [(0, [(0, 1), (0, 4)]), (1, [(0, 3)])],
         blocked := [1],
         cls := Condpor.Targets.Cls.exploration }]
    := by
  decide +kernel

/-- The totals agree with the proved counts: the graphs of `exploreCfgAtF` are
those of `exploreAt` (`exploreCfgAtF_abs`), whose lengths are stated in
`lockT0`, `lockT17`, `lockT4`, `lockT12`. -/
theorem totals_match :
    (exploreCfgAtF progT0 6).length = (lockReport progT0 6).1 ∧
    (exploreCfgAtF progT17 6).length = (lockReport progT17 6).1 ∧
    (exploreCfgAtF progT4 6).length = (lockReport progT4 6).1 ∧
    (exploreCfgAtF progT12 9).length = (lockReport progT12 9).1 := by
  simp only [lockReport, ← exploreCfgAtF_abs, List.length_map, and_self]

end Targets

end Condpor
