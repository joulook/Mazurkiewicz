import Mazurkiewicz.Condpor.Graph

/-!
# Satisfiability and the choice of an outcome

The algorithm uses the symbolic constraints of a graph in two ways: a graph is
consistent only if its literal set `G.F` is satisfiable, and when a deleted
constraint evaluation is rebuilt, one of its two outcomes is the *maximal*
one.

* `Solver`: a satisfiability predicate on finite sets of literals with the
  three properties the theory uses: the empty set is satisfiable, a subset of
  a satisfiable set is satisfiable, and a satisfiable set stays satisfiable
  with one of the two outcomes of any formula. These do not characterise
  Boolean satisfiability (a predicate that accepts `(φ, true)` and
  `(φ, false)` together is allowed); they are what the proofs need.
* `Sem`: an interpretation of formulas over assignments, and the solver it
  defines (`Sem.solver`): a set of literals is satisfiable if some assignment
  gives every formula its outcome.
* `TieBreak`: how the maximal outcome of a constraint evaluation is chosen.
  The choice may depend on a context `K`, a set of literals that is fixed
  during one revisit (the literals of the events the revisit keeps), and on
  the literals `F` of the graph built so far. `inv K F` is the invariant that
  the choice maintains; it implies that `F` is satisfiable.
* `TieBreak.se`: the choice of the algorithm as printed: the formula itself if
  that is satisfiable with `F`, else its negation. It ignores the context.
* `TieBreak.byModel`: the choice of the concolic optimisation: a function
  `solve` gives an assignment for the context, and every outcome is the value
  of the formula under that assignment. That `solve` is a function of the
  literal set is the requirement that the solver's model be deterministic.
-/

namespace Condpor

/-- A satisfiability predicate on finite sets of literals. -/
structure Solver where
  /-- the set of literals is satisfiable -/
  sat : Finset Lit → Prop
  /-- the empty set of constraints is satisfiable -/
  sat_empty : sat ∅
  /-- fewer constraints stay satisfiable -/
  sat_mono : ∀ {F F' : Finset Lit}, F ⊆ F' → sat F' → sat F
  /-- one of the two outcomes of a formula keeps a satisfiable set satisfiable -/
  sat_split : ∀ {F : Finset Lit} (φ : SExpr), sat F →
    sat (insert (φ, true) F) ∨ sat (insert (φ, false) F)

/-- An interpretation of formulas: assignments and the truth of a formula
under an assignment. -/
structure Sem where
  /-- assignments -/
  Asg : Type
  /-- there is an assignment -/
  inh : Nonempty Asg
  /-- the formula holds under the assignment -/
  holds : Asg → SExpr → Prop

namespace Sem

variable (I : Sem)

/-- The assignment gives every formula of `F` its outcome. -/
def Models (m : I.Asg) (F : Finset Lit) : Prop := ∀ l ∈ F, (I.holds m l.1 ↔ l.2 = true)

theorem models_insert {m : I.Asg} {F : Finset Lit} {l : Lit} :
    I.Models m (insert l F) ↔ (I.holds m l.1 ↔ l.2 = true) ∧ I.Models m F := by
  simp [Models]

/-- The solver of an interpretation: some assignment models the set. -/
def solver : Solver where
  sat := fun F => ∃ m, I.Models m F
  sat_empty := by
    obtain ⟨m⟩ := I.inh
    exact ⟨m, fun l hl => absurd hl (Finset.notMem_empty l)⟩
  sat_mono := fun h ⟨m, hm⟩ => ⟨m, fun l hl => hm l (h hl)⟩
  sat_split := by
    rintro F φ ⟨m, hm⟩
    by_cases h : I.holds m φ
    · exact Or.inl ⟨m, (I.models_insert).mpr ⟨by simp [h], hm⟩⟩
    · exact Or.inr ⟨m, (I.models_insert).mpr ⟨by simp [h], hm⟩⟩

end Sem

/-- A rule that chooses the maximal outcome of a constraint evaluation. `K` is
the context, `F` the literals of the graph built so far. -/
structure TieBreak (S : Solver) where
  /-- the invariant of the choice -/
  inv : Finset Lit → Finset Lit → Prop
  /-- the maximal outcome of a formula -/
  pref : Finset Lit → Finset Lit → SExpr → Bool
  /-- a satisfiable context satisfies the invariant with itself -/
  inv_ctx : ∀ {K : Finset Lit}, S.sat K → inv K K
  /-- the invariant implies satisfiability -/
  inv_sat : ∀ {K F : Finset Lit}, inv K F → S.sat F
  /-- the maximal outcome keeps the invariant -/
  inv_step : ∀ {K F : Finset Lit} (φ : SExpr), inv K F → inv K (insert (φ, pref K F φ) F)

namespace TieBreak

open Classical in
/-- The choice of Algorithm 1 as printed (`se`): the formula if it is
satisfiable with the literals so far, else its negation. -/
noncomputable def se (S : Solver) : TieBreak S where
  inv := fun _ F => S.sat F
  pref := fun _ F φ => decide (S.sat (insert (φ, true) F))
  inv_ctx := fun h => h
  inv_sat := fun h => h
  inv_step := by
    intro K F φ h
    by_cases hs : S.sat (insert (φ, true) F)
    · simp [hs]
    · simpa [hs] using (S.sat_split φ h).resolve_left hs

theorem se_pref_iff (S : Solver) (K F : Finset Lit) (φ : SExpr) :
    (se S).pref K F φ = true ↔ S.sat (insert (φ, true) F) := by
  simp [se]

open Classical in
/-- The choice of the concolic optimisation: every outcome is the value of
the formula under the assignment that `solve` gives for the context. -/
noncomputable def byModel (I : Sem) (solve : Finset Lit → I.Asg)
    (hsolve : ∀ K, I.solver.sat K → I.Models (solve K) K) : TieBreak I.solver where
  inv := fun K F => I.Models (solve K) F
  pref := fun K _ φ => decide (I.holds (solve K) φ)
  inv_ctx := fun h => hsolve _ h
  inv_sat := fun h => ⟨_, h⟩
  inv_step := by
    intro K F φ h
    exact (I.models_insert).mpr ⟨by simp, h⟩

theorem byModel_pref_iff (I : Sem) (solve : Finset Lit → I.Asg)
    (hsolve : ∀ K, I.solver.sat K → I.Models (solve K) K) (K F : Finset Lit) (φ : SExpr) :
    (byModel I solve hsolve).pref K F φ = true ↔ I.holds (solve K) φ := by
  simp [byModel]

end TieBreak

end Condpor
