import Mazurkiewicz.Condpor.Rf.Instances
import Mazurkiewicz.Condpor.Variants

/-!
# Line 16 of TruSt's Algorithm 2 as printed

A computed version of the reads-from version (`exploreRV`), as a program,
with one switch: whether `GetConsCO` is applied to the kept events *without*
the revisited read (`false`: the algorithm of `Rf/Alg.lean`) or *with* it
(`true`: line 16 as printed, `GetConsCO(G \ Deleted)`).

The program is not proved equal to `exploreR`, and its `GetConsCO` (`getCoC`)
is not shown to be a `CoChoice` (it enumerates the coherence orders of the
events sorted by a fixed order, so it is a function of the graph; its
fallback when no order is consistent is the empty order). With the switch off it is
compared, on the examples, with the number of reads-from classes that
`exploreR_spec` gives (`exploreR_length_sc`). With the switch on:

* `rfx_printed`: on `x := 1; y := 1 ‖ x := 2; c := y; a := x ‖ x := 3` it
  reports 8 graphs for 6 reads-from classes (`rfx_six`), and two reports have
  the same events, sources and outcomes.

Why: in the two graphs before the revisit of `a` by `x := 3` in which `c`
reads `1` and `a` reads `1`, resp. `2`, both writes to `x` are before `a`, so
in every consistent coherence order the source of `a` is the last write to
`x`. The printed test passes in both, for every `GetConsCO`, and both revisits
give the same graph. Without `a`, one order is chosen for the two graphs and
one of them passes. (That the test passes for every `GetConsCO` is the
argument just given; the Lean statement is for the computed choice
`getCoC`.)
-/

namespace Condpor

open Program

variable {S : Solver} {τ : TieBreak S}

/-- The locations written by the events of `l`. -/
def wrLocs (l : List TEv) : List Loc :=
  (l.filterMap (fun q => match q.act with | .write x _ => some x | _ => none)).dedup

/-- All coherence orders of the writes of `l`: for every written location a
permutation of its writes. -/
def coTuples (l : List TEv) : List (Loc → List TEv) :=
  (wrLocs l).foldr (fun x acc =>
    (perms (l.filter (fun q => q.writesTo x))).flatMap (fun p =>
      acc.map (fun co => Function.update co x p))) [fun _ => []]

/-- `GetConsCO`, computed for SC: the first coherence order, in the
enumeration `coTuples` of the events in a fixed order, for which the
configuration is SC-consistent. The events are sorted first, so the choice
depends on the graph and not on the insertion order. -/
def getCoC (c : Config) : Loc → List TEv :=
  match (coTuples (c.order.insertionSort keyLe)).find? (fun co => (c.withCo co).consC) with
  | some co => co
  | none => fun _ => []

/-- Consistency without coherence, computed: some coherence order is
SC-consistent, and the constraints are satisfiable. -/
def rfConsB (O : Oracle τ) (c : Config) : Bool :=
  (coTuples c.order).any (fun co => (c.withCo co).consC) && O.satB c.abs.F

/-- The kept events of the revisit of `r` by `w`, as a configuration; with or
without `r`. -/
def keptC (c : Config) (r w : TEv) (withR : Bool) : Config :=
  let l := c.order.filter (fun d => decide (d ∈ c.keepC r w) && (withR || decide (d ≠ r)))
  let G := c.abs.restrict l.toFinset
  ⟨c.mem, l, G.rf, G.co, G.pol⟩

/-- The configuration with the coherence order of line 16, computed. -/
def starC (withR : Bool) (c : Config) (r w : TEv) : Config :=
  c.withCo (fun x => getCoC (keptC c r w withR) x ++
    c.order.reverse.filter (fun d => c.deletedB r w d && d.writesTo x))

/-- The steps of the computed reads-from version. -/
def succsRV (withR : Bool) (P : Program) (O : Oracle τ) (c : Config) : List Config :=
  match P.nextC c with
  | none => []
  | some e =>
    match e.act with
    | .read x => ((writesOf c.order x).map (c.addRead e)).filter (rfConsB O)
    | .write x _ =>
      [c.addWrite e .init].filter (rfConsB O) ++
        (c.order.filter (fun r => r.readsLoc x)).flatMap (fun r =>
          if (starC withR c r e).revisitOKB O.prefB r e then
            [c.revisitC r e .init].filter (rfConsB O)
          else [])
    | .cons _ => ([true, false].map (fun b => c.addLoc e (some b))).filter (rfConsB O)
    | _ => [c.addLoc e none].filter (rfConsB O)

/-- The run of the computed reads-from version, to depth `f`. -/
def exploreFromRV (withR : Bool) (P : Program) (O : Oracle τ) : ℕ → Config → List Graph
  | 0, _ => []
  | f + 1, c =>
    if P.nextC c = none then [c.abs]
    else (succsRV withR P O c).flatMap (exploreFromRV withR P O f)

/-- The graphs that the computed reads-from version reports. In both settings
of the switch the argument of `GetConsCO` is a graph of events of the
configuration before the new write `a` is added (in the printed Algorithm 2,
line 16 runs after `Add`, so its `G \\ Deleted` contains `a`; the deleted
events are read here as events of the graph before `a`, as in Algorithm 1). -/
def exploreRV (withR : Bool) (P : Program) (O : Oracle τ) (n : ℕ) : List Graph :=
  exploreFromRV withR P O (P.bound n + 1) (Config.init P.mem)

/-! ### The repaired version on the examples -/

theorem rww_rv : ((exploreRV false rwwProg eqOracleSe 1).map Graph.sig).Perm
    ((exploreC rwwProg eqOracleSe 1).map Graph.sig).dedup := by decide +kernel

/-! ### The example with a forced coherence order -/

/-- `x := 1; y := 1 ‖ x := 2; c := y; a := x ‖ x := 3`. -/
def rfxTab : Tid → List (Option Val) → Option Act
  | 0, [] => some (.write 0 1)
  | 0, [_] => some (.write 1 1)
  | 1, [] => some (.write 0 2)
  | 1, [_] => some (.read 1)
  | 1, [_, _] => some (.read 0)
  | 2, [] => some (.write 0 3)
  | _, _ => none

/-- The program of the example. -/
def rfxProg : Program := mkProg [0, 1, 2] (by decide) rfxTab (fun _ => 0) 3

theorem rfx_classes : ((exploreC rfxProg eqOracleSe 3).map Graph.sig).dedup.length = 6 := by
  decide +kernel

/-- The reads-from version reports 6 graphs on the example, for every choice
of coherence orders and every tie-break (`c` reads `0` or `1`, `a` reads `1`,
`2` or `3`). -/
theorem rfx_six (γ : CoChoice (SC.sym EqSem.solver)) (τ : TieBreak EqSem.solver) :
    (exploreR rfxProg (SC.sym EqSem.solver) γ τ 3).length = 6 := by
  rw [exploreR_length_sc (P := rfxProg) γ eqOracleSe (mkProg_bounded _ _ _ _ _)]
  exact rfx_classes

/-- The computed version with the order chosen without the read: the
reads-from classes, once each. -/
theorem rfx_repaired : ((exploreRV false rfxProg eqOracleSe 3).map Graph.sig).Perm
    ((exploreC rfxProg eqOracleSe 3).map Graph.sig).dedup := by decide +kernel

/-- R-8. Line 16 as printed (the order chosen with the read): 8 reports for 6
reads-from classes, and two reports with the same events, sources and
outcomes. -/
theorem rfx_printed :
    (exploreRV true rfxProg eqOracleSe 3).length = 8 ∧
      ¬ ((exploreRV true rfxProg eqOracleSe 3).map Graph.sig).Nodup := by decide +kernel

/-- The reports of the printed variant are the reads-from classes: none is
lost and none is added; the excess is repetition. -/
theorem rfx_printed_classes : ((exploreRV true rfxProg eqOracleSe 3).map Graph.sig).dedup.Perm
    ((exploreC rfxProg eqOracleSe 3).map Graph.sig).dedup := by decide +kernel

end Condpor
