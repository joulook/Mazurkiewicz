import Mazurkiewicz.Condpor.ExploreC

/-!
# A concrete interpretation: equalities of a symbol with a constant

The formula with code `1000 * s + k` (for `k < 1000`) is `s = k`: the symbol
`s` has the value `k`. Assignments give a natural number to every symbol. This is enough for
the examples of the paper's Section 2.2, where the constraints are `s = 42`
and its negation.

* `EqSem`: the interpretation; `EqSem.solver` is the solver it defines.
* `eqSatB`: a set of literals is satisfiable iff no symbol is given two
  different values by positive literals, and no formula occurs with both
  outcomes (`eqSatB_iff`).
* `eqOracleSe`: the computed solver and tie-break for `TieBreak.se`.
-/

namespace Condpor

/-- The symbol of the formula `s = k`. -/
def fSym (φ : SExpr) : ℕ := φ / 1000
/-- The constant of the formula `s = k`. -/
def fVal (φ : SExpr) : ℕ := φ % 1000

/-- The code of the formula `s = k`. -/
def fEq (s k : ℕ) : SExpr := 1000 * s + k

/-- Equalities `s = k` over assignments of natural numbers. -/
def EqSem : Sem where
  Asg := ℕ → ℕ
  inh := ⟨fun _ => 0⟩
  holds := fun m φ => m (fSym φ) = fVal φ

/-- The test: positive literals agree on every symbol, and no positive
literal is contradicted by a negative one on the same symbol and value. -/
def eqSatB (F : Finset Lit) : Bool :=
  decide (∀ l ∈ F, ∀ l' ∈ F, l.2 = true → fSym l.1 = fSym l'.1 →
    (l'.2 = true → fVal l.1 = fVal l'.1) ∧ (l'.2 = false → fVal l.1 ≠ fVal l'.1))

theorem eqSatB_iff (F : Finset Lit) : eqSatB F = true ↔ EqSem.solver.sat F := by
  unfold eqSatB
  rw [decide_eq_true_eq]
  constructor
  · intro h
    classical
    -- a value above every constant of the set
    let big : ℕ := (F.sup (fun l => fVal l.1)) + 1
    let m : ℕ → ℕ := fun s =>
      if hs : ∃ l ∈ F, l.2 = true ∧ fSym l.1 = s then fVal (Classical.choose hs).1 else big
    refine ⟨m, fun l hl => ?_⟩
    change m (fSym l.1) = fVal l.1 ↔ l.2 = true
    by_cases hs : ∃ l' ∈ F, l'.2 = true ∧ fSym l'.1 = fSym l.1
    · have hm : m (fSym l.1) = fVal (Classical.choose hs).1 := by
        simp only [m, hs, ↓reduceDIte]
      obtain ⟨hc1, hc2, hc3⟩ := Classical.choose_spec hs
      have key := h _ hc1 l hl hc2 hc3
      rw [hm]
      constructor
      · intro heq
        by_contra hn
        exact key.2 (by simpa using hn) heq
      · exact fun ht => key.1 ht
    · have hm : m (fSym l.1) = big := by
        simp only [m, hs, ↓reduceDIte]
      rw [hm]
      constructor
      · intro heq
        have hle : fVal l.1 ≤ F.sup (fun l => fVal l.1) :=
          Finset.le_sup (f := fun l => fVal l.1) hl
        omega
      · intro ht
        exact absurd ⟨l, hl, ht, rfl⟩ hs
  · rintro ⟨m, hm⟩ l hl l' hl' ht hsym
    have h1 : m (fSym l.1) = fVal l.1 := (hm l hl).mpr ht
    have h2 : m (fSym l'.1) = fVal l'.1 ↔ l'.2 = true := hm l' hl'
    rw [← hsym, h1] at h2
    exact ⟨fun h => h2.mpr h, fun h heq => by
      have := h2.mp heq
      rw [h] at this
      cases this⟩

instance : DecidablePred EqSem.solver.sat := fun F =>
  decidable_of_iff _ (eqSatB_iff F)

/-- The computed solver and tie-break for the choice `se`. -/
def eqOracleSe : Oracle (TieBreak.se EqSem.solver) where
  satB := eqSatB
  satB_iff := eqSatB_iff
  prefB := fun _ F φ => eqSatB (insert (φ, true) F)
  prefB_eq := by
    intro K F φ
    rw [Bool.eq_iff_iff, TieBreak.se_pref_iff, eqSatB_iff]

end Condpor
