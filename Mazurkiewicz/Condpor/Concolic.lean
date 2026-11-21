import Mazurkiewicz.Condpor.Examples

/-!
# Section 4.1 of the paper: sparing solver calls

* (O1) The constraints of a graph change only when a constraint evaluation is
  added. So for a read, a write, or a generation, block or error event, the
  extended graph is `M_S`-consistent iff it is `M`-consistent
  (`sym_cons_addRead_iff`, `sym_cons_addWrite_iff`, `sym_cons_addLoc_none_iff`):
  no call of the solver is needed.
* (O2) With an assignment that models the constraints of the graph (the model
  that concolic execution carries), the outcome that the formula has under
  this assignment is satisfiable (`Sem.sat_insert_of_models`): for one of the
  two outcomes of a new constraint evaluation no call of the solver is needed.
* (O3) In a backward revisit, the maximal outcome of a deleted constraint
  evaluation may be taken from the model of the revisit result:
  `TieBreak.byModel`. Theorems 4 and 5 hold for every tie-break, so in
  particular for this one (`complete_byModel`, `eq_of_abs_eq_byModel`,
  `reaches_full_byModel`). The model must be a function of the constraints of
  the revisit result: `solve : Finset Lit → Asg`.
* For the equality constraints of `EqSolver.lean`: `eqSolve`, a computed
  `solve`, and `eqOracleModel`, the computed tie-break `byModel`. The explorer
  with this tie-break finds the same numbers of executions of the examples as
  with `se` (`fig1_count_byModel`, `ex1_count_byModel`), as `exploreC_spec`
  says it must.
-/

namespace Condpor

open Program

variable {P : Program} {M : Model} {S : Solver}

/-! ### (O1) -/

theorem Model.sym_cons_addRead_iff {G : Graph} (hG : G.Wf) {e : TEv} (w : Ev)
    (he : e ∉ G.events) (hs : S.sat G.F) :
    (M.sym S).cons (G.addRead e w) ↔ M.cons (G.addRead e w) := by
  rw [Model.sym_cons_iff, Graph.F_addRead hG w he]
  exact ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩

theorem Model.sym_cons_addWrite_iff {G : Graph} (hG : G.Wf) {e : TEv} (wp : Ev)
    (he : e ∉ G.events) (hs : S.sat G.F) :
    (M.sym S).cons (G.addWrite e wp) ↔ M.cons (G.addWrite e wp) := by
  rw [Model.sym_cons_iff, Graph.F_addWrite hG wp he]
  exact ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩

theorem Model.sym_cons_addLoc_none_iff {G : Graph} {e : TEv} (he : e ∉ G.events)
    (hs : S.sat G.F) :
    (M.sym S).cons (G.addLoc e none) ↔ M.cons (G.addLoc e none) := by
  rw [Model.sym_cons_iff, Graph.F_addLoc_none he]
  exact ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩

/-! ### (O2) -/

open Classical in
/-- The outcome that a formula has under a model of the constraints is
satisfiable with them. -/
theorem Sem.sat_insert_of_models (I : Sem) {m : I.Asg} {F : Finset Lit} (h : I.Models m F)
    (φ : SExpr) : I.solver.sat (insert (φ, decide (I.holds m φ)) F) :=
  ⟨m, (I.models_insert).mpr ⟨by simp, h⟩⟩

/-! ### (O3) -/

section byModel

variable (I : Sem) (solve : Finset Lit → I.Asg)
  (hsolve : ∀ K, I.solver.sat K → I.Models (solve K) K)

/-- Theorem 4 with the model-based tie-break. -/
theorem complete_byModel {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {Gf : Graph}
    (hGf : Gf.Wf) (hEf : P.Exec Gf) (hcf : (M.sym I.solver).cons Gf) (hff : P.Full Gf) :
    ∃ c, Reach P (M.sym I.solver) (TieBreak.byModel I solve hsolve) c ∧ c.abs = Gf :=
  complete hn hM hGf hEf hcf hff

/-- Theorem 5(a) with the model-based tie-break. -/
theorem eq_of_abs_eq_byModel {c1 c2 : Config}
    (h1 : Reach P (M.sym I.solver) (TieBreak.byModel I solve hsolve) c1)
    (h2 : Reach P (M.sym I.solver) (TieBreak.byModel I solve hsolve) c2)
    (h : c1.abs = c2.abs) : c1 = c2 :=
  Reach.eq_of_abs_eq h1 h2 h

/-- Theorem 5(b) with the model-based tie-break. -/
theorem reaches_full_byModel {n : ℕ} (hn : P.Bounded n) (hM : M.Extensible) {c : Config}
    (hc : Reach P (M.sym I.solver) (TieBreak.byModel I solve hsolve) c) :
    ∃ c', Relation.ReflTransGen
      (Step P (M.sym I.solver) (TieBreak.byModel I solve hsolve)) c c' ∧ P.Full c'.abs :=
  hc.reaches_full hn hM

end byModel

/-! ### The model-based tie-break for equality constraints, computed -/

/-- A model of a satisfiable set of equality literals: a symbol with a
positive literal gets its value, any other symbol a value above every
constant of the set. -/
def eqSolve (F : Finset Lit) : ℕ → ℕ := fun s =>
  match ((F.filter (fun l => l.2 = true ∧ fSym l.1 = s)).image (fun l => fVal l.1)).min with
  | some k => k
  | none => F.sup (fun l => fVal l.1) + 1

theorem eqSolve_models (F : Finset Lit) (h : EqSem.solver.sat F) :
    EqSem.Models (eqSolve F) F := by
  have hB := (eqSatB_iff F).mpr h
  unfold eqSatB at hB
  rw [decide_eq_true_eq] at hB
  intro l hl
  change eqSolve F (fSym l.1) = fVal l.1 ↔ l.2 = true
  unfold eqSolve
  cases hmin : ((F.filter (fun l' => l'.2 = true ∧ fSym l'.1 = fSym l.1)).image
      (fun l' => fVal l'.1)).min with
  | top =>
    have hempty := Finset.min_eq_top.mp hmin
    simp only
    constructor
    · intro heq
      have hle : fVal l.1 ≤ F.sup (fun l => fVal l.1) :=
        Finset.le_sup (f := fun l => fVal l.1) hl
      omega
    · intro ht
      have : fVal l.1 ∈ (F.filter (fun l' => l'.2 = true ∧ fSym l'.1 = fSym l.1)).image
          (fun l' => fVal l'.1) :=
        Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, ht, rfl⟩, rfl⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty _)
  | coe k =>
    have hk := Finset.mem_of_min hmin
    obtain ⟨l0, hl0, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hl0F, hl0t, hl0s⟩ := Finset.mem_filter.mp hl0
    have key := hB l0 hl0F l hl hl0t hl0s
    simp only
    constructor
    · intro heq
      by_contra hn
      exact key.2 (by simpa using hn) heq
    · exact fun ht => key.1 ht

/-- The computed solver and tie-break for the model-based choice. -/
def eqOracleModel : Oracle (TieBreak.byModel EqSem eqSolve eqSolve_models) where
  satB := eqSatB
  satB_iff := eqSatB_iff
  prefB := fun K _ φ => decide (eqSolve K (fSym φ) = fVal φ)
  prefB_eq := by
    intro K F φ
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    exact (TieBreak.byModel_pref_iff EqSem eqSolve eqSolve_models K F φ).symm

theorem fig1_count_byModel : (exploreC fig1 eqOracleModel 3).length = 6 := by decide +kernel

theorem ex1_count_byModel : (exploreC ex1 eqOracleModel 4).length = 4 := by decide +kernel

end Condpor
