import Mazurkiewicz.Condpor.Counts

/-!
# The algorithm as printed: four non-examples

Algorithm 1 is formalised in `Alg.lean` with four readings that differ from
the printed text (see its header). Here each reading is undone in turn, in the
computed explorer, and the result is compared with the explorer of
`ExploreC.lean`, which lists every full consistent execution once
(`exploreC_spec`).

`Variant` has two hooks: the test that a revisit must pass, and the coherence
places that are tried for the revisiting write. `exploreV V` is the explorer
with these hooks; with `Variant.std` it is `exploreC` (`succsV_std`).

* N0, the deletion set (`Variant.noRevisit`). As printed, the events deleted
  by a revisit of `r` by the new write `a` are the events added after `r` that
  are not causally before `a`; the write `a` itself is such an event
  (`printed_deleted_self`), and the chain of maximal additions cannot both add
  `a` and end in the graph without `a`. So no revisit passes. Then
  `r := x ‖ x := 1` (reader first) loses the execution in which the read reads
  from the write (`n0_lost`).
* N1, `se` on the formula of the event (`Variant.seOnLabel`). After `SetSYM`
  the event carries the constraint of its own outcome, so each outcome is the
  preferred one: a deleted constraint evaluation always passes. Then the
  program of Example 1 gets six reports for its four executions, and two
  reports agree on the source of the read and the outcome of the constraint
  (`n1_duplicate`).

A count below the number of executions shows that an execution is lost. A
count above it shows that the variant reports a graph twice or reports
something that is not a full consistent execution; which of the two is not
proved here (the variants have no soundness theorem). In either case the
variant does not satisfy the specification of the explorer.
* N2, no coherence choice after a revisit (`Variant.coInit`, `Variant.coLast`).
  The revisiting write gets one place, the one `Add` gave: first or last. In
  both cases `x := 1 ‖ a := x ‖ x := 2` loses an execution (`n2_lost_init`,
  `n2_lost_last`).
* N3, a model that is not a function of the revisit result
  (`Variant.modelOf`). The program is an analogue of the example of Section
  4.1, not the same program: `gen s ‖ b := x ‖ assume(s = 42) ‖ x := 1`, with
  `s = 42` for `a > 42`, the generation in a thread of its own, and without
  the constraint `a > 0` of the writing thread (so the revisit result has no
  constraint). It shows the same mechanism: if the model used in the
  predecessor with `s = 42` makes `s = 42` true and the one used in the
  predecessor with `s ≠ 42` makes it false, both revisits pass and there are
  six reports for four executions (`n3_duplicate`); with the two models
  swapped no revisit passes and the executions in which the read reads from
  the write are lost (`n3_lost`).
* Two witnesses for the list of points for the paper: with the exit, the run
  on the program of Fig. 1 reports an erroneous graph and no list
  (`fig1_exit`); the two tie-breaks can choose different outcomes
  (`se_ne_byModel`).
-/

namespace Condpor

open Program

variable {S : Solver} {τ : TieBreak S}

/-- The hooks of a variant of the explorer. -/
structure Variant where
  /-- the test of a revisit of `r` by `w` in `c` -/
  okB : Config → TEv → TEv → Bool
  /-- the coherence places tried for `w`, among the candidates -/
  places : Config → TEv → TEv → List Ev → List Ev

/-- The steps of the variant. -/
def succsV (V : Variant) (P : Program) (O : Oracle τ) (c : Config) : List Config :=
  match P.nextC c with
  | none => []
  | some e =>
    match e.act with
    | .read x =>
      ((writesOf c.order x).filter (fun w => (c.addRead e w).consS O)).map (c.addRead e)
    | .write x _ =>
      ((writesOf c.order x).filter (fun wp => (c.addWrite e wp).consS O)).map (c.addWrite e) ++
        (c.order.filter (fun r => r.readsLoc x)).flatMap (fun r =>
          if V.okB c r e then
            ((V.places c r e
              (writesOf (c.order.filter (fun d => decide (d ∈ c.keepC r e))) x)).filter
              (fun wp => (c.revisitC r e wp).consS O)).map (c.revisitC r e)
          else [])
    | .cons _ =>
      ([true, false].filter (fun b => (c.addLoc e (some b)).consS O)).map
        (fun b => c.addLoc e (some b))
    | _ => if (c.addLoc e none).consS O then [c.addLoc e none] else []

/-- The run of the variant, to depth `f`. -/
def exploreFromV (V : Variant) (P : Program) (O : Oracle τ) : ℕ → Config → List Graph
  | 0, _ => []
  | f + 1, c =>
    if c.consS O then
      if P.nextC c = none then [c.abs] else (succsV V P O c).flatMap (exploreFromV V P O f)
    else []

/-- The graphs that the variant reports. -/
def exploreV (V : Variant) (P : Program) (O : Oracle τ) (n : ℕ) : List Graph :=
  exploreFromV V P O (P.bound n + 1) (Config.init P.mem)

/-- The algorithm of `Alg.lean`. -/
def Variant.std (O : Oracle τ) : Variant where
  okB := fun c r w => c.revisitOKB O.prefB r w
  places := fun _ _ _ l => l

theorem succsV_std (P : Program) (O : Oracle τ) (c : Config) :
    succsV (Variant.std O) P O c = succsC P O c := rfl

theorem exploreFromV_std (P : Program) (O : Oracle τ) (f : ℕ) (c : Config) :
    exploreFromV (Variant.std O) P O f c = exploreFromC P O f c := by
  induction f generalizing c with
  | zero => rfl
  | succ f ih =>
    unfold exploreFromV exploreFromC
    have h : exploreFromV (Variant.std O) P O f = exploreFromC P O f := funext ih
    rw [succsV_std, h]

theorem exploreV_std (P : Program) (O : Oracle τ) (n : ℕ) :
    exploreV (Variant.std O) P O n = exploreC P O n :=
  exploreFromV_std P O _ _

/-! ### N0: the deletion set as printed -/

/-- The new write satisfies the printed condition for being deleted by its own
revisit: it was added after the read, and it is not causally before itself. -/
theorem printed_deleted_self {c : Config} {r w : TEv} {wp : Ev} (hr : r ∈ c.order)
    (hw : w ∉ c.order) (hac : Maz.Acyclic (c.addWrite w wp).abs.porfStep) :
    (c.addWrite w wp).lt r w ∧ ¬ (c.addWrite w wp).abs.porf (.th w) (.th w) := by
  refine ⟨?_, hac (.th w)⟩
  change (w :: c.order).Before w r
  exact (List.before_cons_iff_of_notMem hw).mpr (Or.inl ⟨rfl, hr⟩)

/-- No revisit passes. -/
def Variant.noRevisit : Variant where
  okB := fun _ _ _ => false
  places := fun _ _ _ l => l

/-- `r := x ‖ x := 1`, reader first. -/
def rwTab : Tid → List (Option Val) → Option Act
  | 0, [] => some (.read 0)
  | 1, [] => some (.write 0 1)
  | _, _ => none

/-- The program of N0. -/
def rwProg : Program := mkProg [0, 1] (by decide) rwTab (fun _ => 0) 1

/-- N0: without revisits, the execution in which the read reads from the write
is not found; it is an execution (the explorer finds it). -/
theorem n0_lost :
    (exploreC rwProg eqOracleSe 1).any (fun G =>
      decide (G.rf ⟨0, 0, .read 0⟩ = some (.th ⟨1, 0, .write 0 1⟩))) = true ∧
    (exploreV Variant.noRevisit rwProg eqOracleSe 1).all (fun G =>
      !decide (G.rf ⟨0, 0, .read 0⟩ = some (.th ⟨1, 0, .write 0 1⟩))) = true := by
  decide +kernel

/-! ### N1: `se` on the formula that the event carries -/

/-- A deleted constraint evaluation always passes; the other events are tested
as in the algorithm. -/
def Variant.seOnLabel (O : Oracle τ) : Variant where
  okB := fun c r w =>
    !c.plusPorfB w (.th r) (.th w) &&
      c.order.all (fun d => !(c.deletedB r w d || decide (d = r)) ||
        (decide d.IsCons || c.maxAddedB (O.prefB (c.ctxC r w)) d w))
  places := fun _ _ _ l => l

/-- N1: with `se` read on the formula of the event, Example 1 gets six reports
for its four executions, and two reports agree on the source of the read and
the outcome of the constraint. -/
theorem n1_duplicate :
    (exploreC ex1 eqOracleSe 4).length = 4 ∧
    (exploreV (Variant.seOnLabel eqOracleSe) ex1 eqOracleSe 4).length = 6 ∧
    ¬ ((exploreV (Variant.seOnLabel eqOracleSe) ex1 eqOracleSe 4).map
      (fun G => (G.rf ex1r, G.pol ex1s))).Nodup := by
  decide +kernel

/-! ### N2: no coherence choice after a revisit -/

/-- The revisiting write is placed first in coherence. -/
def Variant.coInit (O : Oracle τ) : Variant where
  okB := fun c r w => c.revisitOKB O.prefB r w
  places := fun _ _ _ _ => [.init]

/-- The revisiting write is placed last in coherence. -/
def Variant.coLast (O : Oracle τ) : Variant where
  okB := fun c r w => c.revisitOKB O.prefB r w
  places := fun c r w _ => [(c.abs.restrict (c.keepC r w)).maxWrite w.loc]

/-- `x := 1 ‖ a := x ‖ x := 2`. -/
def wrwTab : Tid → List (Option Val) → Option Act
  | 0, [] => some (.write 0 1)
  | 1, [] => some (.read 0)
  | 2, [] => some (.write 0 2)
  | _, _ => none

/-- The program of N2. -/
def wrwProg : Program := mkProg [0, 1, 2] (by decide) wrwTab (fun _ => 0) 1

/-- N2, the write placed first: five reports for six executions. -/
theorem n2_lost_init :
    (exploreC wrwProg eqOracleSe 1).length = 6 ∧
    (exploreV (Variant.coInit eqOracleSe) wrwProg eqOracleSe 1).length = 5 := by
  decide +kernel

/-- N2, the write placed last: five reports for six executions. -/
theorem n2_lost_last :
    (exploreV (Variant.coLast eqOracleSe) wrwProg eqOracleSe 1).length = 5 := by
  decide +kernel

/-! ### N3: a model that depends on the predecessor -/

/-- `gen s ‖ b := x ‖ assume(s = 42) ‖ x := 1`. -/
def n3Tab : Tid → List (Option Val) → Option Act
  | 0, [] => some (.gen 1)
  | 1, [] => some (.read 0)
  | 2, [] => some (.cons (fEq 1 42))
  | 2, [some b] => if b = 0 then some .block else none
  | 3, [] => some (.write 0 1)
  | _, _ => none

/-- The program of N3. -/
def n3Prog : Program := mkProg [0, 1, 2, 3] (by decide) n3Tab (fun _ => 0) 2

/-- The evaluation of `s = 42` in N3. -/
def n3s : TEv := ⟨2, 0, .cons (fEq 1 42)⟩

/-- The maximal outcome of a deleted constraint evaluation is the truth of its
formula in a model that depends on the predecessor: `flip = false`: the model
of each predecessor satisfies the constraint that the predecessor has;
`flip = true`: the two models are swapped. -/
def Variant.modelOf (flip : Bool) : Variant where
  okB := fun c r w =>
    !c.plusPorfB w (.th r) (.th w) &&
      c.order.all (fun d => !(c.deletedB r w d || decide (d = r)) ||
        c.maxAddedB (fun _ _ => (c.pol n3s == some true) != flip) d w)
  places := fun _ _ _ l => l

/-- N3 with models as in the paper's example (each satisfies the constraint of
its predecessor): six reports for four executions. -/
theorem n3_duplicate :
    (exploreC n3Prog eqOracleSe 2).length = 4 ∧
    (exploreV (Variant.modelOf false) n3Prog eqOracleSe 2).length = 6 := by
  decide +kernel

/-- N3 with the two models swapped: no revisit passes, and the executions in
which the read reads from the write are lost (two reports, four executions). -/
theorem n3_lost :
    (exploreV (Variant.modelOf true) n3Prog eqOracleSe 2).length = 2 ∧
    (exploreC n3Prog eqOracleSe 2).any (fun G =>
      decide (G.rf ⟨1, 0, .read 0⟩ = some (.th ⟨3, 0, .write 0 1⟩))) = true ∧
    (exploreV (Variant.modelOf true) n3Prog eqOracleSe 2).all (fun G =>
      !decide (G.rf ⟨1, 0, .read 0⟩ = some (.th ⟨3, 0, .write 0 1⟩))) = true := by
  decide +kernel

/-! ### Two witnesses -/

/-- With the exit, the run on the program of Fig. 1 reports an erroneous graph
(and so not the list of its six executions). -/
theorem fig1_exit : ∃ G, exploreX fig1 eqOracleSe ErrOracle.label 3 = .inl G := by
  have h : (exploreX fig1 eqOracleSe ErrOracle.label 3).isLeft = true := by decide +kernel
  cases hx : exploreX fig1 eqOracleSe ErrOracle.label 3 with
  | inl G => exact ⟨G, rfl⟩
  | inr l => rw [hx] at h; cases h

/-- The two tie-breaks differ: with no constraint so far, `se` prefers
`s = 42`, and the model of the empty set of constraints (`eqSolve`) makes it
false. -/
theorem se_ne_byModel :
    eqOracleSe.prefB ∅ ∅ (fEq 1 42) = true ∧ eqOracleModel.prefB ∅ ∅ (fEq 1 42) = false := by
  decide +kernel

end Condpor
